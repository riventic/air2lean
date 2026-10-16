import ZigLean.Sep.Full.Auto

/-!
# Structs as their fields (`StructLayout`, engine ledger #78, #79)

A struct that the translator generates (its `Enc` writes `Enc.fields N [(o, Enc.encode x), …]` and
decodes `do pure { f := ← Enc.decodeAt bs o, … }`) has a layout (`ZigLean/Sep/Full/Struct.lean`),
which `fsym` derives from the decoding (`structLayoutOf?`): its `LawfulEnc` (`lawfulEncOf?`, so
owned bytes that are its encoding fold into its `pts`), its `pts` split into its fields' `pts` and
its padding's bytes, and those joined back (views at a stuck step, `viewAtoms`). The structs below
are written as the translator writes them (`tests/roadmap/alloc-fba/AllocFba/Gen.lean`). A packed
struct, an encoding that does not write each field where its decoding reads it, and a wrong value
get nothing (fail closed).
-/

namespace SepAuto.Structs

open Zig Zig.Full Zig.Full.FAssn

/-- Two words (the `FixedBufferAllocator`'s struct). -/
structure Fba where
  end_index : BitVec 64
  buffer : Zig.Slice
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Fba where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.end_index), (8, Zig.Enc.encode v.buffer)]
  decode bs := do pure { end_index := ← Zig.Enc.decodeAt bs 0, buffer := ← Zig.Enc.decodeAt bs 8 }

/-- A byte, 7 bytes of padding and a word; the fields in another order than their bytes. -/
structure Pad where
  w : BitVec 64
  b : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Pad where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(8, Zig.Enc.encode v.w), (0, Zig.Enc.encode v.b)]
  decode bs := do pure { w := ← Zig.Enc.decodeAt bs 8, b := ← Zig.Enc.decodeAt bs 0 }

/-- A struct with a struct field. -/
structure Outer where
  tag : BitVec 64
  fba : Fba
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Outer where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.tag), (8, Zig.Enc.encode v.fba)]
  decode bs := do pure { tag := ← Zig.Enc.decodeAt bs 0, fba := ← Zig.Enc.decodeAt bs 8 }

/-- A packed struct (`Packed` bits): no layout. -/
structure Q where
  lo : BitVec 4
  hi : BitVec 4
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Q 8 where
  toBits v := ((Zig.Packed.toBits v.lo).setWidth 8 <<< 0) ||| ((Zig.Packed.toBits v.hi).setWidth 8 <<< 4)
  ofBits b := { lo := Zig.Packed.get b 0, hi := Zig.Packed.get b 4 }

instance : Zig.Enc Q where
  size := 1
  align := 1
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 8 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

/-- A mutated encoding: it writes the fields where the decoding does not read them. -/
structure Swapped where
  x : BitVec 64
  y : BitVec 32
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Swapped where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(8, Zig.Enc.encode v.x), (0, Zig.Enc.encode v.y)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0, y := ← Zig.Enc.decodeAt bs 8 }

/-! ## A stored struct's bytes are its `pts` (`LawfulEnc`, ledger #78) -/

theorem fold (p : Ptr) (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) :
    EUpd (up (bytesAt p A 24 .stack (Enc.encode v))) (up (pts p 8 v)) := by
  fsym_entail

/-- The post of a store into a block (`FTotalTriple.storeBlock`). -/
theorem fold_write (p : Ptr) (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) :
    EUpd (up (bytesAt p A 24 .stack (writeBytes (Array.replicate 24 .undef) 0 (Enc.encode v))))
      (up (pts p 8 v)) := by
  fsym_entail

/-- A store of a whole struct: the rule's `LawfulEnc` is the struct's derived one. -/
theorem store_whole (q : Ptr) (v w : Fba) :
    FTotalTriple (up (pts q 8 v)) (Zig.store 8 q w) (fun _ => up (pts q 8 w)) := by
  fsym

theorem fold_nested (p : Ptr) (A : Nat) (v : Outer) (ha : (A + p.off.toNat) % 8 = 0) :
    EUpd (up (bytesAt p A 32 .stack (Enc.encode v))) (up (pts p 8 v)) := by
  fsym_entail

/-- The bytes of a global as its fields (a fold at the type's alignment, then a split). -/
theorem fold_split (p : Ptr) (b : BlockId) (hb : p.block = some b) (A : Nat) (v : Fba)
    (ha : A % 8 = 0) (h0 : p.off = 0) :
    EUpd (up (bytesAt p A 24 .global (Enc.encode v)))
      (up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) := by
  fsym_entail

/-! ## A struct's `pts` is its fields' and its padding's (ledger #79) -/

theorem split (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Fba) :
    EUpd (up (pts s 8 v)) (up (pts s 8 v.end_index) ⋆ up (pts (s.add 8) 8 v.buffer)) := by
  fsym_entail

theorem join (s : Ptr) (b : BlockId) (hb : s.block = some b) (e : BitVec 64) (sl : Slice) :
    EUpd (up (pts s 8 e) ⋆ up (pts (s.add 8) 8 sl))
      (up (pts s 8 ({ end_index := e, buffer := sl } : Fba))) := by
  fsym_entail

theorem split_pad (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Pad) :
    EUpd (up (pts s 8 v)) (up (pts s 1 v.b) ⋆ up (padBytes (s.add 1) 7) ⋆ up (pts (s.add 8) 8 v.w)) := by
  fsym_entail

theorem join_pad (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Pad) :
    EUpd (up (pts s 1 v.b) ⋆ up (padBytes (s.add 1) 7) ⋆ up (pts (s.add 8) 8 v.w)) (up (pts s 8 v)) := by
  fsym_entail

/-- A field of a field (two splits). -/
theorem split_nested (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Outer) :
    EUpd (up (pts s 8 v))
      (up (pts s 8 v.tag) ⋆ up (pts (s.add 8) 8 v.fba.end_index) ⋆ up (pts (s.add 16) 8 v.fba.buffer)) := by
  fsym_entail

/-! ## Fail closed -/

set_option linter.unusedVariables false in
/-- A packed struct has no layout: its `pts` is not split. -/
example (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Q) : True := by
  fail_if_success
    have : EUpd (up (pts s 1 v)) (up (pts s 1 v.lo) ⋆ up (pts s 1 v.hi)) := by
      fsym_entail; done
  trivial

set_option linter.unusedVariables false in
/-- An encoding that does not write each field where its decoding reads it gets no `LawfulEnc`:
its bytes do not fold. -/
example (p : Ptr) (A : Nat) (v : Swapped) (ha : (A + p.off.toNat) % 8 = 0) : True := by
  fail_if_success
    have : EUpd (up (bytesAt p A 16 .stack (Enc.encode v))) (up (pts p 8 v)) := by
      fsym_entail; done
  trivial

set_option linter.unusedVariables false in
/-- A split gives the struct's own fields, not other values. -/
example (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Fba) (e : BitVec 64)
    (he : e ≠ v.end_index) : True := by
  fail_if_success
    have : EUpd (up (pts s 8 v)) (up (pts s 8 e) ⋆ up (pts (s.add 8) 8 v.buffer)) := by
      fsym_entail; done
  trivial

set_option linter.unusedVariables false in
/-- A join needs every piece: without the padding's bytes there is no struct. -/
example (s : Ptr) (b : BlockId) (hb : s.block = some b) (v : Pad) : True := by
  fail_if_success
    have : EUpd (up (pts s 1 v.b) ⋆ up (pts (s.add 8) 8 v.w)) (up (pts s 8 v)) := by
      fsym_entail; done
  trivial

end SepAuto.Structs
