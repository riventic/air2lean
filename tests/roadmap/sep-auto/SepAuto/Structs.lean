import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Region

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

/-- First-field nesting provides distinct intermediate states for the view-retry control. -/
structure NestedFba where
  inner : Fba
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc NestedFba where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.inner)]
  decode bs := do pure { inner := ← Zig.Enc.decodeAt bs 0 }

structure TwiceNestedFba where
  inner : NestedFba
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc TwiceNestedFba where
  size := 24
  align := 8
  encode v := Zig.Enc.fields 24 [(0, Zig.Enc.encode v.inner)]
  decode bs := do pure { inner := ← Zig.Enc.decodeAt bs 0 }

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

/-- A real store followed by typed folding and field splitting retains the actual address
needed by an invariant, even though the typed points themselves hide byte metadata. -/
theorem store_fields_keep_address (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) :
    FTotalTriple
      (up (bytesAt p A 24 .stack (Array.replicate 24 .undef)) ⋆ bext b 24 .stack)
      (do Zig.store 8 p v; pure ())
      (fun _ => (up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer) ⋆
        bext b 24 .stack) ⋆ known b A) := by
  have hw : (Enc.encode v).size = 24 := by
    change (Enc.fields 24 [(0, Enc.encode v.end_index), (8, Enc.encode v.buffer)]).size = 24
    apply fields_size
    simp only [partSizes, List.map_cons, List.map_nil, LawfulEnc.size_encode]
    decide
  fsym

/-- The caller's contract needs the innermost word, so three distinct first-field views must
remain eligible at the same command. An opaque command excludes the direct field-load rule. -/
theorem view_chain_three (p : Ptr) (v : TwiceNestedFba) (op : MemM Unit)
    (hStep : FTotalTriple (up (pts p 8 v.inner.inner.end_index)) op
      (fun _ => up (pts p 8 v.inner.inner.end_index))) :
    FTotalTriple (up (pts p 8 v)) op (fun _ => Junk) := by
  fsym [hStep]

/-- Reopening an existential address must find the knowledge committed before typed views. -/
theorem store_fields_known_exists (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) :
    FTotalTriple
      (up (bytesAt p A 24 .stack (Array.replicate 24 .undef)) ⋆ bext b 24 .stack)
      (do Zig.store 8 p v; pure ())
      (fun _ => FAssn.ex fun A' =>
        (up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer) ⋆
          bext b 24 .stack) ⋆ known b A') := by
  have hw : (Enc.encode v).size = 24 := by
    change (Enc.fields 24 [(0, Enc.encode v.end_index), (8, Enc.encode v.buffer)]).size = 24
    apply fields_size
    simp only [partSizes, List.map_cons, List.map_nil, LawfulEnc.size_encode]
    decide
  fsym

/-- A committed knowledge update may need a region view while leaving an ordinary quantified
pure fact. That fact must not be dispatched as a direct update retry. -/
theorem return_known_quantified_update_side (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A S : Nat) (bs : Array Byte) (hn : 0 < bs.size) (R : Nat → FAssn) :
    FTotalTriple (up (bytesAt p A S .stack bs)) (pure ())
      (fun _ => (up (regionIn p A S .stack 1 bs) ⋆ known b A) ⋆
        ⟪∀ n : Nat, EUpd (R n) (R n)⟫) := by
  fsym <;> exact fun _ => EUpd.of_imp (fun _ h => h)

theorem known_bytes_requested (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A S : Nat) (K : BlockKind) (bs : Array Byte) (hn : 0 < bs.size) :
    EUpd (up (bytesAt p A S K bs)) (up (bytesAt p A S K bs) ⋆ known b A) := by
  fsym_entail

/-- Distinct requested copies exercise knowledge indices and bounded retries. -/
theorem known_bytes_requested_twice (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A S : Nat) (K : BlockKind) (bs : Array Byte) (hn : 0 < bs.size) :
    EUpd (up (bytesAt p A S K bs))
      (up (bytesAt p A S K bs) ⋆ (known b A ⋆ known b A)) := by
  fsym_entail

/-- Existing knowledge satisfies a fresh address witness without adding another atom. -/
theorem known_bytes_existing_exists (p : Ptr) (b : BlockId)
    (A S : Nat) (K : BlockKind) (bs : Array Byte) :
    EUpd (up (bytesAt p A S K bs) ⋆ known b A)
      (FAssn.ex fun A' => up (bytesAt p A S K bs) ⋆ known b A') := by
  fsym_entail

/-- Region planning must determine the requested address before unrelated existing knowledge
can cover it speculatively. -/
theorem known_region_existing_exists (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A A₀ S : Nat) (K : BlockKind) (bs : Array Byte) (hn : 0 < bs.size) :
    EUpd (up (regionIn p A S K 1 bs) ⋆ known b A₀)
      (FAssn.ex fun A' => up (regionIn p A' S K 1 bs) ⋆ known b A') := by
  fsym_entail

/-- An existential block stays for ordinary matching; an unrelated earlier region must not
choose the shared address witness before the retained region determines it. -/
theorem known_regions_existing_block_exists (p q : Ptr) (b c : BlockId)
    (hp : p.block = some b) (hq : q.block = some c) (A B S T : Nat) (K L : BlockKind)
    (xs ys : Array Byte) (hx : 0 < xs.size) (hy : 0 < ys.size) :
    EUpd (up (regionIn p A S K 1 xs) ⋆ up (regionIn q B T L 1 ys) ⋆ known c B)
      (FAssn.ex fun b' => FAssn.ex fun A' =>
        up (regionIn p A S K 1 xs) ⋆ up (regionIn q A' T L 1 ys) ⋆ known b' A') := by
  fsym_entail

/-- No knowledge request retains the exact public store result. -/
theorem store_no_known_request (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) :
    FTotalTriple
      (up (bytesAt p A 24 .stack (Array.replicate 24 .undef)) ⋆ bext b 24 .stack)
      (Zig.store 8 p v)
      (fun _ => up (bytesAt p A 24 .stack
        (writeBytes (Array.replicate 24 .undef) 0 (Enc.encode v))) ⋆ bext b 24 .stack) := by
  have hw : (Enc.encode v).size = 24 := by
    change (Enc.fields 24 [(0, Enc.encode v.end_index), (8, Enc.encode v.buffer)]).size = 24
    apply fields_size
    simp only [partSizes, List.map_cons, List.map_nil, LawfulEnc.size_encode]
    decide
  fsym

theorem free_fields (p : Ptr) (b : BlockId) (hb : p.block = some b) (h0 : p.off = 0)
    (e : BitVec 64) (sl : Slice) :
    FTotalTriple
      ((up (pts p 8 e) ⋆ up (pts (p.add 8) 8 sl)) ⋆ bext b 24 .stack)
      (Zig.free p) (fun _ => emp) := by
  fsym

theorem free_fields_stack (p : Ptr) (b : BlockId) (hb : p.block = some b) (h0 : p.off = 0)
    (e : BitVec 64) (sl : Slice) (t S D c : Nat) :
    FTotalTriple
      (((up (pts p 8 e) ⋆ up (pts (p.add 8) 8 sl)) ⋆ bext b 24 .stack) ⋆
        (ent t (some b) D c ⋆ sp t S (D + c)))
      (Zig.free p) (fun _ => sp t S D) := by
  fsym

/-- A rule demanding all 24 bytes must reject the first 8-byte candidate and join the adjacent
16-byte region, at an arbitrary alignment. -/
theorem free_regions_8_16 (p : Ptr) (b : BlockId) (hb : p.block = some b) (h0 : p.off = 0)
    (A S a : Nat) (bs₈ bs₁₆ : Array Byte) (h₈ : bs₈.size = 8) (h₁₆ : bs₁₆.size = 16) :
    FTotalTriple
      ((up (regionIn p A S .stack a bs₈) ⋆ up (regionIn (p.add 8) A S .stack a bs₁₆)) ⋆
        bext b 24 .stack)
      (Zig.free p) (fun _ => emp) := by
  fsym

/-- A late state branch substitutes the demanded size; matching data must follow the same
recorded substitutions as caller terms, while the original size premise is proved normally. -/
theorem free_regions_state_if_size (c : Prop) [Decidable c] (p : Ptr) (b : BlockId)
    (hb : p.block = some b) (h0 : p.off = 0) (A S a len : Nat)
    (bs₈ bs₁₆ : Array Byte) (h₈ : bs₈.size = 8) (h₁₆ : bs₁₆.size = 16)
    (hlen : len + 0 = 24) :
    FTotalTriple
      (if c then
        ⟪len = 24⟫ ⋆ ((up (regionIn p A S .stack a bs₈) ⋆
          up (regionIn (p.add 8) A S .stack a bs₁₆)) ⋆ bext b 24 .stack)
      else
        (up (regionIn (p.add 8) A S .stack a bs₁₆) ⋆ up (regionIn p A S .stack a bs₈)) ⋆
          (⟪len = 24⟫ ⋆ bext b 24 .stack))
      (Zig.free p) (fun _ => emp) := by
  fsym [FTotalTriple.free_region (Sz := len)]

/-- Expected failure, ledger `carve-size-probes`: carving excludes case facts. Trying an ordinary
size proof here regresses the existing partial-header `n = 24` large-state control. The positive
goal is retained unchanged until a general solution preserves that protected search boundary. -/
example (p : Ptr) (b : BlockId) (hb : p.block = some b) (h0 : p.off = 0)
    (A S a x y : Nat) (bs : Array Byte)
    (h : (bs.size + x = 24 ∧ x = 0) ∨ (bs.size + y = 24 ∧ y = 0)) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S .stack a bs) ⋆ bext b 24 .stack)
        (Zig.free p) (fun _ => emp) := by
      fsym
  trivial

/-- An unresolved rule size must let the token determine its byte and size witnesses. -/
theorem region_size_from_token (p : Ptr) (b : BlockId) (hb : p.block = some b) (A S : Nat)
    (tok : Array Byte → Nat → FAssn) (op : MemM Unit)
    (hRule : ∀ (cs : Array Byte) (k : Nat), cs.size = k + 1 →
      FTotalTriple (up (regionIn p A S .stack 1 cs) ⋆ tok cs k) op (fun _ => emp))
    (bs : Array Byte) (k : Nat) (hsize : bs.size = k + 1) :
    FTotalTriple (up (regionIn p A S .stack 8 bs) ⋆ tok bs k) op (fun _ => emp) := by
  fsym [hRule]

/-- Two tokens of one head must still be matched distinctly while the size is unresolved. -/
theorem region_size_from_two_tokens (p : Ptr) (b : BlockId) (hb : p.block = some b) (A S : Nat)
    (tok : Array Byte → Nat → FAssn) (op : MemM Unit)
    (hRule : ∀ (cs ds : Array Byte) (k j : Nat), cs.size = k + 1 →
      FTotalTriple (up (regionIn p A S .stack 1 cs) ⋆ (tok cs k ⋆ tok ds j)) op (fun _ => emp))
    (bs ds : Array Byte) (k j : Nat) (hsize : bs.size = k + 1) :
    FTotalTriple (up (regionIn p A S .stack 8 bs) ⋆ (tok bs k ⋆ tok ds j)) op (fun _ => emp) := by
  fsym [hRule]

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
/-- Eight owned bytes do not meet the complete 24-byte release rule. Inverse region/byte views
must stop at a repeated retry state, so this failure is bounded at the ordinary heartbeat cap. -/
example (p : Ptr) (b : BlockId) (hb : p.block = some b) (h0 : p.off = 0)
    (A S a : Nat) (bs : Array Byte) (h₈ : bs.size = 8) : True := by
  fail_if_success
    have bad : FTotalTriple (up (regionIn p A S .stack a bs) ⋆ bext b 24 .stack)
        (Zig.free p) (fun _ => emp) := by fsym; done
  trivial

set_option linter.unusedVariables false in
example (p : Ptr) (b b' : BlockId) (hb : p.block = some b) (hne : b' ≠ b)
    (A S : Nat) (K : BlockKind) (bs : Array Byte) (hn : 0 < bs.size) : True := by
  fail_if_success
    have bad : EUpd (up (bytesAt p A S K bs))
        (up (bytesAt p A S K bs) ⋆ known b' A) := by fsym_entail
  trivial

set_option linter.unusedVariables false in
example (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A S : Nat) (K : BlockKind) (bs : Array Byte) (hn : 0 < bs.size) : True := by
  fail_if_success
    have bad : EUpd (up (bytesAt p A S K bs))
        (up (bytesAt p A S K bs) ⋆ known b (A + 1)) := by fsym_entail
  trivial

set_option linter.unusedVariables false in
example (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A S : Nat) (K : BlockKind) : True := by
  fail_if_success
    have bad : EUpd (up (bytesAt p A S K #[]))
        (up (bytesAt p A S K #[]) ⋆ known b A) := by fsym_entail
  trivial

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

/-! ## No failure cached under a limit (`limitedRun`)

A struct nested deeper than the nesting budget of a field's derivation (`encFieldOf?`, 8) gets no
field; the structs inside it, queried after it in the same run, still get theirs (the failures
under the limit are not cached). -/

/-- A word, then structs of one struct field each. -/
structure N0 where
  w : BitVec 64

instance : Zig.Enc N0 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.w)]
  decode bs := do pure { w := ← Zig.Enc.decodeAt bs 0 }

structure N1 where
  x : N0

instance : Zig.Enc N1 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N2 where
  x : N1

instance : Zig.Enc N2 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N3 where
  x : N2

instance : Zig.Enc N3 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N4 where
  x : N3

instance : Zig.Enc N4 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N5 where
  x : N4

instance : Zig.Enc N5 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N6 where
  x : N5

instance : Zig.Enc N6 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N7 where
  x : N6

instance : Zig.Enc N7 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N8 where
  x : N7

instance : Zig.Enc N8 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

structure N9 where
  x : N8

instance : Zig.Enc N9 where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.x)]
  decode bs := do pure { x := ← Zig.Enc.decodeAt bs 0 }

open Lean Meta Zig.Full.Auto in
/-- **No field failure cached under the nesting budget** (`encFieldOf?`): `N9`'s word is past
the budget; `N2`'s, queried next in the same run, is found. -/
example : True := by
  run_tac withRunCaches do
    let w := mkApp (mkConst ``BitVec) (mkNatLit 64)
    if (← encFieldOf? (mkConst ``N9) w 0).isSome then
      throwError "N9's word within the nesting budget: deepen the chain"
    if (← encFieldOf? (mkConst ``N2) w 0).isNone then
      throwError "N2's word: the failure under the nesting budget was cached"
  trivial

/-! ## Requested knowledge across a successful raw-to-typed view -/

/-- An opaque command needs both exact fields and address knowledge after folding. Every
unrelated resource remains in the explicit frame; the command cannot be solved by inlining. -/
theorem view_step_known_frame (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) (R : FAssn) (op : MemM Unit)
    (hStep : FTotalTriple
      ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆ known b A)
      op (fun _ =>
        (up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆ known b A)) :
    FTotalTriple (up (bytesAt p A 24 .stack (Enc.encode v)) ⋆ R) op
      (fun _ => ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆
        known b A) ⋆ R) := by
  fsym [hStep]

/-- Repeated knowledge remains repeated inside one combined demand. The heap fields and
arbitrary exclusive frame are each retained once, without contracting their occurrences. -/
theorem view_step_known_twice (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) (R : FAssn) (op : MemM Unit)
    (hStep : FTotalTriple
      ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆ (known b A ⋆ known b A))
      op (fun _ =>
        (up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆
          (known b A ⋆ known b A))) :
    FTotalTriple (up (bytesAt p A 24 .stack (Enc.encode v)) ⋆ R) op
      (fun _ => ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆
        (known b A ⋆ known b A)) ⋆ R) := by
  fsym [hStep]

/-- Existing knowledge is counted once against the FULL requested multiplicity. The view
must derive one missing copy; it must not cover an additional request with the old copy twice. -/
theorem view_step_existing_known_twice (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) (R : FAssn) (op : MemM Unit)
    (hStep : FTotalTriple
      ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆ (known b A ⋆ known b A))
      op (fun _ =>
        (up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆
          (known b A ⋆ known b A))) :
    FTotalTriple ((up (bytesAt p A 24 .stack (Enc.encode v)) ⋆ known b A) ⋆ R) op
      (fun _ => ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆
        (known b A ⋆ known b A)) ⋆ R) := by
  fsym [hStep]

/-- A rejected update's other block must not choose closePre's structural view or supply
its knowledge. Only the successful update's local combined demand is used. -/
theorem return_update_known_frame (p q : Ptr) (b c : BlockId)
    (hb : p.block = some b) (hq : q.block = some c) (hne : b ≠ c)
    (A B : Nat) (v w : Fba) (ha : (A + p.off.toNat) % 8 = 0) (R T : FAssn)
    (bad : EUpd
      ((up (pts q 8 w.end_index) ⋆ up (pts (q.add 8) 8 w.buffer)) ⋆ known c B) T)
    (good : EUpd
      ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆ known b A) T) :
    FTotalTriple (up (bytesAt p A 24 .stack (Enc.encode v)) ⋆ R)
      (pure ()) (fun _ => T ⋆ R) := by
  fsym [bad, good]

/-- closePre can view a residual precondition after committing a real knowledge update.
Its actual state already has both copies, so the full demand must not add either again. -/
theorem return_update_known_existing_twice (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A : Nat) (v : Fba) (ha : (A + p.off.toNat) % 8 = 0) (R T : FAssn)
    (update : EUpd
      ((up (pts p 8 v.end_index) ⋆ up (pts (p.add 8) 8 v.buffer)) ⋆ (known b A ⋆ known b A)) T) :
    FTotalTriple ((up (bytesAt p A 24 .stack (Enc.encode v)) ⋆ known b A) ⋆ R)
      (pure ()) (fun _ => T ⋆ R) := by
  fsym [update]

/-- A zero-sized lawful encoding still folds without a knowledge request or a new
positive-size premise on the successful view. -/
theorem zero_view_no_request {T : Type} [Enc T] [LawfulEnc T] (v : T)
    (hz : Enc.size T = 0) (p : Ptr) (A S a : Nat)
    (ha : (A + p.off.toNat) % a = 0) (R : FAssn) (op : MemM Unit)
    (hStep : FTotalTriple (up (pts p a v)) op (fun _ => up (pts p a v))) :
    FTotalTriple (up (bytesAt p A S .stack (Enc.encode v)) ⋆ R)
      op (fun _ => up (pts p a v) ⋆ R) := by
  fsym [hStep]

set_option linter.unusedVariables false in
/-- The first address can be preserved, but the actual last known-only failure is not
reclassified as a hint or silently dropped from the demand. -/
example (p : Ptr) (b : BlockId) (hb : p.block = some b)
    (A S : Nat) (K : BlockKind) (bs : Array Byte) (hn : 0 < bs.size) : True := by
  fail_if_success
    have : EUpd (up (bytesAt p A S K bs))
        (up (bytesAt p A S K bs) ⋆ (known b A ⋆ known b (A + 1))) := by
      fsym_entail
  trivial

open Lean Meta Zig.Full.Auto in
/-- The consumer contract retains the true target, including a known-only, opaque or
multi-atom target. Prefix multiplicity is distinct from request deduplication. -/
example (b : BlockId) (A : Nat) (X R : FAssn) : True := by
  run_tac do
    let b := (← getLocalDeclFromUserName `b).toExpr
    let A := (← getLocalDeclFromUserName `A).toExpr
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let k ← mkAppM ``Zig.Full.known #[b, A]
    let lastTarget ← mkAppM ``Zig.Full.known #[b, ← mkAppM ``Nat.add #[A, mkNatLit 1]]
    let (target, hints) := viewDemand lastTarget
    unless target == lastTarget && hints.isEmpty do
      throwError "known-only failure became a hint"
    let (target, hints) := viewDemand (mkSep (mkSep k k) lastTarget)
    unless target == lastTarget && hints == #[k, k] do
      throwError "combined demand lost its true target or repeated knowledge"
    let (target, hints) := viewDemand (mkSep k X)
    unless target == X && hints == #[k] do
      throwError "opaque failed target was unfolded"
    let multiple := mkSep X R
    let (target, hints) := viewDemand (mkSep k multiple)
    unless target == multiple && hints == #[k] do
      throwError "multi-atom failed target was reduced to its last leaf"
    let (target, hints) := viewDemand multiple
    unless target == multiple && hints.isEmpty do
      throwError "ordinary multi-atom request changed"
  trivial

end SepAuto.Structs
