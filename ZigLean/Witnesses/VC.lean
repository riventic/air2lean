import ZigLean.VC.Rules
import ZigLean.Witnesses.Sep

/-!
# Non-vacuity and liveness witnesses: verification-condition programs

Concrete programs for the soundness lemmas of `ZigLean/VC/*.lean` (`docs/claim-strength.md`):
`ret ()` with the post `emp`, and an annotated loop whose body leaves at once.
-/

namespace Zig.Witness

open Assn VC

nonvacuity_witness MemProgram.eval.eq_1 := ⟨Unit, (), trivial⟩
nonvacuity_witness ResultProgram.eval.eq_1 := ⟨Unit, (), trivial⟩

nonvacuity_witness MemProgram.sound := ⟨Unit, .ret (), fun _ => emp, Admit.emp⟩
liveness_witness MemProgram.sound := ⟨Unit, .ret (), fun _ => emp, Live.of_empty rfl ⟨_, rfl⟩⟩

nonvacuity_witness MemProgram.verify := ⟨Unit, emp, .ret (), fun _ => emp, fun _ h => h, Admit.emp⟩
liveness_witness MemProgram.verify :=
  ⟨Unit, emp, .ret (), fun _ => emp, fun _ h => h, Live.of_empty rfl ⟨_, rfl⟩⟩

nonvacuity_witness MemProgram.sound_of := ⟨Unit, .ret (), pure (), rfl, fun _ => emp, Admit.emp⟩
liveness_witness MemProgram.sound_of :=
  ⟨Unit, .ret (), pure (), rfl, fun _ => emp, Live.of_empty rfl ⟨_, rfl⟩⟩

nonvacuity_witness triple_intro :=
  ⟨Unit, .ret (), pure (), emp, fun _ => emp, rfl, fun _ h => h, Admit.emp⟩
liveness_witness triple_intro :=
  ⟨Unit, .ret (), pure (), emp, fun _ => emp, rfl, fun _ h => h, Live.of_empty rfl ⟨_, rfl⟩⟩

/-- The iteration contract of a loop whose body leaves at once, with no bytes owned. -/
theorem exitBody_annotated (hF : Heap) (s : Unit) (m : Mem) (h : Heap) (hd : Heap.Disjoint h hF)
    (hm : m.heap = h ∪ hF) (hi : emp h) (hs : m.Seq) :
    ∃ e s' m' h', (exitBody.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧ m'.Seq ∧
      if (fun _ : Unit => false) e then emp h' ∧ (fun _ : Unit => 0) s' < (fun _ : Unit => 0) s
      else (fun _ _ => emp : Unit → Unit → Assn) e s' h' :=
  ⟨(), s, m, h, rfl, hd, hm, hs, hi⟩

nonvacuity_witness MemProgram.annotatedLoop._proof_2 :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ => emp, fun _ => 0, fun _ _ => emp,
    exitBody_annotated, (), Admit.emp⟩
liveness_witness MemProgram.annotatedLoop._proof_2 :=
  ⟨Unit, Unit, exitBody, fun _ => false, fun _ => emp, fun _ => 0, fun _ _ => emp,
    exitBody_annotated, (),
    Live.of_total (TotalTriple.loop_ghost exitBody _ _ (fun _ _ => emp) exitBody_step () 0) Admit.emp⟩

end Zig.Witness
