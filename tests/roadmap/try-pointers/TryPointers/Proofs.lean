import TryPointers.Gen
import ZigLean.Sep.Try
import ZigLean.Sep.Discard

open Zig
open scoped Zig

namespace TryPointersProofs

-- The tag-only helper rule has no initialized-payload precondition. Generated functions
-- also perform an unused whole-object read, requiring readableBytes for that full range.
-- Payload and cleanup ownership is retained through framing; use Triple.bind afterwards.
theorem success_with_frame {α : Type} [Enc α] (p : Ptr) (a : Nat) (R : Assn) :
    Triple (errorTag α p a none ∗ R) (tryPayloadPtr α a p)
      (fun result => (⌜result = .ok (errPayloadPtr α p)⌝ ∗ errorTag α p a none) ∗ R) :=
  Triple.tryPayloadPtr.frame

theorem error_with_frame {α : Type} [Enc α] (p : Ptr) (a : Nat) (e : ErrName) (R : Assn) :
    Triple (errorTag α p a (some e) ∗ R) (tryPayloadPtr α a p)
      (fun result => (⌜result = .error e⌝ ∗ errorTag α p a (some e)) ∗ R) :=
  Triple.tryPayloadPtr.frame

theorem whole_read_with_frame (p : Ptr) (n a : Nat) (R : Assn) (hn : 0 < n) :
    Triple (readableBytes p n a ∗ R) (loadDiscardBytes n a p)
      (fun _ => readableBytes p n a ∗ R) :=
  (Triple.loadDiscardBytes hn).frame

-- Both model layouts preserve provenance and use the compiler-model payload offset.
theorem byte_payload_address (p : Ptr) : errPayloadPtr (BitVec 8) p = p.add 2 := rfl
theorem wide_payload_address (p : Ptr) : errPayloadPtr (BitVec 64) p = p := by
  change p.add (0 : Int) = p
  cases p
  simp [Ptr.add]


-- This reference keeps the generated whole-object read and the second tag read on error.
def payloadProgram (α : Type) [Enc α] (n a : Nat) (p : Ptr) :
    MemM (Except ErrName Ptr) := do
  loadDiscardBytes n a p
  match ← tryPayloadPtr α a p with
  | .error _ => pure (.error (← errCodeAt α a p))
  | .ok q => pure (.ok q)

-- MUTANT_BRIDGE_BEGIN: payload8_program
-- These equalities name the actual checked source-generated definitions.
theorem payload8_program (p : Ptr) :
    TryPointers.payload8 p = payloadProgram (BitVec 8) 4 2 p := by
  funext m
  -- The generated MM wrapper carries a local-state pair through each effect. Split
  -- the actual effect outcomes before reducing those pairs and the return wrapper.
  cases hread : loadDiscardBytes 4 2 p m with
  | none => simp [TryPointers.payload8, payloadProgram, zig_unfold, hread]
  | some read =>
    cases read with
    | error failure => simp [TryPointers.payload8, payloadProgram, zig_unfold, hread]
    | ok read =>
      rcases read with ⟨u, m₁⟩
      cases htag : tryPayloadPtr (BitVec 8) 2 p m₁ with
      | none => simp [TryPointers.payload8, payloadProgram, zig_unfold, hread, htag]
      | some tag =>
        cases tag with
        | error failure => simp [TryPointers.payload8, payloadProgram, zig_unfold, hread, htag]
        | ok tag =>
          rcases tag with ⟨result, m₂⟩
          cases result with
          | ok q => simp [TryPointers.payload8, payloadProgram, zig_unfold, hread, htag]
          | error name =>
            cases hcode : errCodeAt (BitVec 8) 2 p m₂ with
            | none => simp [TryPointers.payload8, payloadProgram, zig_unfold, hread, htag, hcode]
            | some code =>
              cases code <;> simp [TryPointers.payload8, payloadProgram, zig_unfold, hread, htag, hcode]
-- MUTANT_BRIDGE_END: payload8_program

theorem payload64_program (p : Ptr) :
    TryPointers.payload64 p = payloadProgram (BitVec 64) 16 8 p := by
  funext m
  -- The generated MM wrapper carries a local-state pair through each effect. Split
  -- the actual effect outcomes before reducing those pairs and the return wrapper.
  cases hread : loadDiscardBytes 16 8 p m with
  | none => simp [TryPointers.payload64, payloadProgram, zig_unfold, hread]
  | some read =>
    cases read with
    | error failure => simp [TryPointers.payload64, payloadProgram, zig_unfold, hread]
    | ok read =>
      rcases read with ⟨u, m₁⟩
      cases htag : tryPayloadPtr (BitVec 64) 8 p m₁ with
      | none => simp [TryPointers.payload64, payloadProgram, zig_unfold, hread, htag]
      | some tag =>
        cases tag with
        | error failure => simp [TryPointers.payload64, payloadProgram, zig_unfold, hread, htag]
        | ok tag =>
          rcases tag with ⟨result, m₂⟩
          cases result with
          | ok q => simp [TryPointers.payload64, payloadProgram, zig_unfold, hread, htag]
          | error name =>
            cases hcode : errCodeAt (BitVec 64) 8 p m₂ with
            | none => simp [TryPointers.payload64, payloadProgram, zig_unfold, hread, htag, hcode]
            | some code =>
              cases code <;> simp [TryPointers.payload64, payloadProgram, zig_unfold, hread, htag, hcode]

/-- One assertion owns the entire object. Only its two tag bytes must decode;
all payload/padding bytes may be undefined. Separate tag ownership is not assumed. -/
def readableUnion (α : Type) [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName) : Assn :=
  fun h => ∃ A S K bs,
    (A + p.off.toNat) % a = 0 ∧ bs.size = n ∧ 0 < n ∧
    (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size ∧
    (A + p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) % (Nat.min a 2) = 0 ∧
    errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure e ∧
    bytesAt p A S K bs h

private theorem readableUnion_tag_run {α : Type} [Enc α] {p : Ptr} {n a : Nat}
    {e : Option ErrName} {m : Mem} {h hF : Heap}
    (hp : readableUnion α p n a e h) (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (tryPayloadPtr α a p).run m =
      pure ((match e with | none => .ok (errPayloadPtr α p) | some name => .error name), m') ∧
      (∀ name, e = some name → (errCodeAt α a p).run m = pure (name, m')) ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨A, S, K, bs, -, -, -, hbnd, ha, he, hb⟩ := hp
  let eo := (errUnionOffsets (Enc.size α) (Enc.align α)).1
  obtain ⟨block, blk, hacc, -, -, -, hx⟩ := bytesAt_access
    (p := p) (q := p.add eo) (k := eo) (n := 2) (a := Nat.min a 2) hb hm
    rfl (by decide) hbnd ha
  have hl := loadBytes_run hacc
    (noRace_of_singleThread hs.single block (p.off.toNat + eo) 2 .read)
  rw [hx] at hl
  refine ⟨m.recordAt block (p.off.toNat + eo) 2 .read, ?_, ?_, ?_, hs.recordAt _ _ _ _⟩
  · simp only [StateT.run] at hl
    cases e <;> simp [tryPayloadPtr, zig_unfold, hl, he, eo]
  · intro name hn
    subst e
    simp only [StateT.run] at hl
    simp [errCodeAt, zig_unfold, hl, he, eo]
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- Both actual generated layouts preserve the whole owned object and arbitrary frame.
The first read covers every object byte. On error the generated error-code read is retained. -/
theorem payloadProgram_run {α : Type} [Enc α] {p : Ptr} {n a : Nat}
    {e : Option ErrName} {m : Mem} {h hF : Heap}
    (hp : readableUnion α p n a e h) (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (payloadProgram α n a p).run m =
      pure ((match e with | none => .ok (errPayloadPtr α p) | some name => .error name), m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  have hpWhole := hp
  obtain ⟨A, S, K, bs, ha, hn, hpos, -, -, -, hb⟩ := hpWhole
  have hw : readableBytes p n a h := ⟨A, S, K, bs, ha, hn, hb⟩
  obtain ⟨m₁, hread, hm₁, hs₁⟩ := readableBytes_discard_run hw hm hpos hs
  obtain ⟨m₂, htag, -, hm₂, hs₂⟩ := readableUnion_tag_run
    (α := α) (p := p) (n := n) (a := a) (e := e) (m := m₁) (h := h) (hF := hF) hp hm₁ hs₁
  cases e with
  | none =>
    refine ⟨m₂, ?_, hm₂, hs₂⟩
    simp only [StateT.run] at hread htag
    simp [payloadProgram, zig_unfold, hread, htag]
  | some name =>
    obtain ⟨m₃, -, hcode', hm₃, hs₃⟩ := readableUnion_tag_run
      (α := α) (p := p) (n := n) (a := a) (e := some name) (m := m₂)
      (h := h) (hF := hF) hp hm₂ hs₂
    have herr := hcode' name rfl
    refine ⟨m₃, ?_, hm₃, hs₃⟩
    simp only [StateT.run] at hread htag herr
    simp [payloadProgram, zig_unfold, hread, htag, herr]

theorem payloadProgram_owned {α : Type} [Enc α] (p : Ptr) (n a : Nat) (e : Option ErrName) :
    Triple (readableUnion α p n a e) (payloadProgram α n a p)
      (fun result => ⌜result = (match e with
        | none => .ok (errPayloadPtr α p) | some name => .error name)⌝ ∗
        readableUnion α p n a e) := by
  cases e <;> apply Triple.of_run
  all_goals
    intro m h hF hd hm hp hs
    obtain ⟨m', hr, hm', hs'⟩ := payloadProgram_run
      (α := α) (p := p) (n := n) (a := a) (m := m) (h := h) (hF := hF) hp hm hs
    exact ⟨_, m', h, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

theorem payload8_owned (p : Ptr) (e : Option ErrName) (R : Assn) :
    Triple (readableUnion (BitVec 8) p 4 2 e ∗ R) (TryPointers.payload8 p)
      (fun result => (⌜result = (match e with
        | none => .ok (errPayloadPtr (BitVec 8) p) | some name => .error name)⌝ ∗
        readableUnion (BitVec 8) p 4 2 e) ∗ R) := by
  rw [payload8_program]
  exact (payloadProgram_owned p 4 2 e).frame

theorem payload64_owned (p : Ptr) (e : Option ErrName) (R : Assn) :
    Triple (readableUnion (BitVec 64) p 16 8 e ∗ R) (TryPointers.payload64 p)
      (fun result => (⌜result = (match e with
        | none => .ok (errPayloadPtr (BitVec 64) p) | some name => .error name)⌝ ∗
        readableUnion (BitVec 64) p 16 8 e) ∗ R) := by
  rw [payload64_program]
  exact (payloadProgram_owned p 16 8 e).frame

end TryPointersProofs
