import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Typed

/-!
# Fields of a stored struct (`EncField`, `docs/proof-automation.md` §Fields)

A struct of generated code is stored as one typed value `up (pts p a h)` and read and written
whole and by field: a field load gives `h.f`, a field store makes the value `{ h with f := w }`,
a field inside a field (a slice's `len` in a header) likewise. `fsym` derives the `EncField` of
the field from the struct's encoding (`Auto.lean` `encFieldOf?`), for any struct the translator
writes. The structs below are written as the translator writes them
(`std.ArrayListUnmanaged(u32)`'s header of Zig 0.17: a slice, a capacity and a
`debug.SafetyLock`, an enum in a struct).
-/

namespace SepAuto.Fields

open Zig Zig.Full Zig.Full.FAssn

structure Lock_State where
  bits : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lock_State where
  size := 8
  align := 8
  encode v := Zig.Enc.encode v.bits
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    pure ⟨b⟩

structure Lock where
  state : Lock_State
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lock where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure Hdr where
  items : Zig.Slice
  capacity : BitVec 64
  pointer_stability : Lock
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Hdr where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.items), (16, Zig.Enc.encode v.capacity), (24, Zig.Enc.encode v.pointer_stability)]
  decode bs := do pure { items := ← Zig.Enc.decodeAt bs 0, capacity := ← Zig.Enc.decodeAt bs 16, pointer_stability := ← Zig.Enc.decodeAt bs 24 }

/-- A field load. -/
theorem load_capacity (p : Ptr) (h : Hdr) :
    FTotalTriple (up (pts p 8 h)) (load (BitVec 64) 8 (p.add 16))
      (fun r => ⟪r = h.capacity⟫ ⋆ up (pts p 8 h)) := by
  fsym

/-- A field of a field (the slice's length), and a struct-typed field. -/
theorem load_len_lock (p : Ptr) (h : Hdr) :
    FTotalTriple (up (pts p 8 h))
      (do let n ← load (BitVec 64) 8 (p.add 8); let l ← load Lock 8 (p.add 24); pure (n, l))
      (fun r => ⟪r = (h.items.len, h.pointer_stability)⟫ ⋆ up (pts p 8 h)) := by
  fsym

/-- Field stores at byte 0 (the slice's pointer, a field of a field) and inside, then a load of
the whole value and of the slice. -/
theorem store_then_whole (p q : Ptr) (h : Hdr) (n c : BitVec 64) :
    FTotalTriple (up (pts p 8 h))
      (do store 8 p q; store 8 (p.add 8) n; store 8 (p.add 16) c
          let s ← load Slice 8 p; let w ← load Hdr 8 p; pure (s, w))
      (fun r => ⟪r = (⟨q, n⟩, { h with items := ⟨q, n⟩, capacity := c })⟫ ⋆
        up (pts p 8 { h with items := ⟨q, n⟩, capacity := c })) := by
  fsym

/-- `addOneAssumeCapacity`'s accesses: the length read twice and incremented in place, the
capacity read; the header afterwards. -/
theorem add_one (p : Ptr) (ptr : Ptr) (len cap : BitVec 64) (L : Lock)
    (hl : len.toNat < cap.toNat) :
    FTotalTriple (up (pts p 8 ({ items := ⟨ptr, len⟩, capacity := cap, pointer_stability := L } : Hdr)))
      (do
        let n ← load (BitVec 64) 8 (p.add 8)
        let c ← load (BitVec 64) 8 (p.add 16)
        if n.toNat < c.toNat then
          store 8 (p.add 8) (n + 1)
          let n' ← load (BitVec 64) 8 (p.add 8)
          pure n'
        else pure n)
      (fun r => ⟪r = len + 1⟫ ⋆
        up (pts p 8 ({ items := ⟨ptr, len + 1⟩, capacity := cap, pointer_stability := L } : Hdr))) := by
  fsym

/-- A header value by its parts (a module's definition). -/
def hdr (ptr : Ptr) (len cap : BitVec 64) (L : Lock) : Hdr :=
  { items := ⟨ptr, len⟩, capacity := cap, pointer_stability := L }

/-- `addOneAssumeCapacity` with its buffer: the overflow-checked increment stored, the new item's
pointer returned; the header afterwards by the module's definition (equal up to arithmetic in
its fields). -/
theorem add_one_item (p ptr : Ptr) (len cap : BitVec 64) (L : Lock) (bs : Array Byte) (b : BlockId)
    (A S : Nat) (K : BlockKind) (hb : ptr.block = some b) (hl : len.toNat < cap.toNat)
    (hs : bs.size = 4 * cap.toNat) :
    FTotalTriple (up (pts p 8 (hdr ptr len cap L)) ⋆ up (regionIn ptr A S K 4 bs))
      (do
        let n ← load (BitVec 64) 8 (p.add 8)
        let c ← load (BitVec 64) 8 (p.add 16)
        if n.toNat < c.toNat then
          let n1 ← (StateT.lift (Zig.add false n 1) : MemM (BitVec 64))
          store 8 (p.add 8) n1
          let s ← load Slice 8 p
          ptrProject s.ptr (·.elem 4 n)
        else throw .panic)
      (fun r => ⟪r = ptr.elem 4 len⟫ ⋆ up (pts p 8 (hdr ptr (len + 1) cap L)) ⋆
        up (regionIn ptr A S K 4 bs)) := by
  fsym

set_option linter.unusedVariables false in
/-- Rejected: a load that straddles two fields reads no field. -/
example (p : Ptr) (h : Hdr) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 8 h)) (load (BitVec 64) 8 (p.add 12))
        (fun r => ⟪r = h.capacity⟫ ⋆ up (pts p 8 h)) := by
      fsym
  trivial

end SepAuto.Fields
