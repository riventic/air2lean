import ZigLean.Sep.Triple

/-! Ownership rules for pointer-form try. Only the tag is accessed. Frame payload ownership
separately: its bytes may remain undefined, and success preserves their address and contents.
These rules require sequential memory; concurrent access needs the existing race obligations. -/

namespace Zig
open Assn

/-- Own the error tag, with its actual access alignment. No payload bytes are required. -/
def errorTag (α : Type) [Enc α] (p : Ptr) (a : Nat) (e : Option ErrName) : Assn := fun h =>
  let q := p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1
  ∃ A S K, (A + q.off.toNat) % (Nat.min a 2) = 0 ∧ bytesAt q A S K (errBytes e) h

/-- A successful tag read changes only the memory access record, never owned/frame bytes. -/
theorem errorTag_try_run {α : Type} [Enc α] {p : Ptr} {a : Nat} {e : Option ErrName}
    {m : Mem} {h hF : Heap} (hp : errorTag α p a e h) (hm : m.heap = h ∪ hF)
    (hst : m.Seq) :
    ∃ m', (tryPayloadPtr α a p).run m =
      pure ((match e with | none => .ok (errPayloadPtr α p) | some name => .error name), m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  let q := p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1
  obtain ⟨A, S, K, ha, hb⟩ := hp
  have he : (errBytes e).size = 2 := by cases e <;> rfl
  obtain ⟨block, blk, hacc, -, -, -, hx⟩ := bytesAt_access
    (p := q) (q := q) (k := 0) (n := 2) (a := Nat.min a 2) hb hm
    (by simp [Ptr.add]) (by decide) (by omega) (by simpa using ha)
  simp only [Nat.add_zero] at hx hacc
  have hl := loadBytes_run hacc (noRace_of_singleThread hst.single block q.off.toNat 2 .read)
  have hex : (errBytes e).extract 0 2 = errBytes e := by rw [← he]; simp
  rw [hx, hex] at hl
  refine ⟨m.recordAt block q.off.toNat 2 .read, ?_, ?_, hst.recordAt _ _ _ _⟩
  · simp only [StateT.run] at hl
    simp only [tryPayloadPtr, StateT.run_bind]
    cases e <;> simp [errOfBytes, errBytes, pure, ExceptT.pure, ExceptT.mk, bind,
      ExceptT.bind, ExceptT.bindCont, StateT.run, liftM, monadLift, MonadLift.monadLift,
      StateT.lift, StateT.pure, hl, q]
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- Success returns the original payload address; error retains the original error name.
The tag assertion and arbitrary framed payload/cleanup ownership remain available. -/
theorem Triple.tryPayloadPtr {α : Type} [Enc α] {p : Ptr} {a : Nat} {e : Option ErrName} :
    Triple (errorTag α p a e) (Zig.tryPayloadPtr α a p)
      (fun r => ⌜r = (match e with | none => .ok (errPayloadPtr α p) | some name => .error name)⌝ ∗
        errorTag α p a e) := by
  apply Triple.of_run
  intro m h hF hd hm hp hs
  obtain ⟨m', hr, hm', hs'⟩ := errorTag_try_run hp hm hs
  exact ⟨_, m', h, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

/-- The payload pointer keeps allocation provenance. -/
theorem errPayloadPtr_block (α : Type) [Enc α] (p : Ptr) :
    (errPayloadPtr α p).block = p.block := rfl

/-- The payload pointer changes only the compiler-model payload offset. -/
theorem errPayloadPtr_offset (α : Type) [Enc α] (p : Ptr) :
    (errPayloadPtr α p).off = p.off + (errUnionOffsets (Enc.size α) (Enc.align α)).2 := rfl

end Zig
