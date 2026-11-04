import Proofs.Pointers.Gen
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.WitnessStart

/-!
# Separation-logic proofs about `examples/pointers/pointers.zig`

`swap` exchanges the values of two `u32` that do not overlap (`pts p 4 x ⋆ pts q 4 y`), and
`swap(p, p)` keeps the value. The rest of the memory is unchanged. Both are total: the run
returns. `fsym` walks the generated code with the library's load and store rules; the strength
log (`tests/roadmap/strength-log/ProofsPointers.lean`) gives back the legacy statements.
-/

open Pointers Zig Zig.Full FAssn

theorem swap_sep (p q : Ptr) (x y : BitVec 32) :
    FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (swap p q)
      (fun _ => up (pts p 4 y) ⋆ up (pts q 4 x)) := by
  fsym

/-- `swap(p, p)` keeps the value. -/
theorem swap_self_sep (p : Ptr) (x : BitVec 32) :
    FTotalTriple (up (pts p 4 x)) (swap p p) (fun _ => up (pts p 4 x)) := by
  fsym

/-! ## Memory-backed recursion with a stack budget

This is a contract for the current generated `MemM` program, in explicit unmetered mode.
Each invocation, including `n = 0`, pays its modeled frame and restores that charge on return.
It is not an AIR/native certificate or a cost bound: recursive memory remains outside
`Pointers.AirCert`'s fragment, and native frame adequacy retains STK-01.
-/

namespace Pointers

/-- The mathematical increment of `addDown`: `n + (n - 1) + ... + 1`. -/
def sumDown : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumDown n

end Pointers

private theorem sumDown_ge (n : Nat) : n ≤ sumDown n := by
  cases n with
  | zero => simp [sumDown]
  | succ n => simp only [sumDown]; exact Nat.le_add_right _ _

private theorem sumDown_step (n k : BitVec 32) (h : k.toNat + 1 = n.toNat) :
    sumDown n.toNat = n.toNat + sumDown k.toNat := by
  rw [← h]
  rfl

private theorem addDown_sum_step {n k : BitVec 32} {x y z : BitVec 64}
    (hz : z.toNat = n.toNat) (hy : y.toNat = x.toNat + z.toNat)
    (hk : k.toNat + (1#32).toNat = n.toNat) :
    y.toNat + sumDown k.toNat = x.toNat + sumDown n.toNat := by
  have hs := sumDown_step n k (by simpa using hk)
  rw [hy, hz, hs]
  exact Nat.add_assoc _ _ _

private theorem addDown_bound_step {n k : BitVec 32} {x y z : BitVec 64}
    (hb : x.toNat + sumDown n.toNat < 2 ^ 64)
    (hz : z.toNat = n.toNat) (hy : y.toNat = x.toNat + z.toNat)
    (hk : k.toNat + (1#32).toNat = n.toNat) :
    y.toNat + sumDown k.toNat < 2 ^ 64 := by
  rw [addDown_sum_step hz hy hk]
  exact hb

private structure AddDownInvocation where
  n : BitVec 32
  value : BitVec 64
  depth : Nat

private def addDownPre (p : Ptr) (t S : Nat) (a : AddDownInvocation) : FAssn :=
  ⟪a.value.toNat + sumDown a.n.toNat < 2 ^ 64 ∧
    a.depth + frameBase * (a.n.toNat + 1) ≤ S⟫ ⋆
    (up (pts p 8 a.value) ⋆ (cur t ⋆ (sp t S a.depth ⋆ unmetered)))

private def addDownPost (p : Ptr) (t S : Nat) (a : AddDownInvocation) (_ : Unit) : FAssn :=
  up (pts p 8 (BitVec.ofNat 64 (a.value.toNat + sumDown a.n.toNat))) ⋆
    (cur t ⋆ (sp t S a.depth ⋆ unmetered))

private theorem addDown_group (p : Ptr) (t S : Nat) (a : AddDownInvocation) :
    FTotalTriple (addDownPre p t S a) (addDown p a.n) (addDownPost p t S a) := by
  refine FTotalTriple.rec_group (fun a : AddDownInvocation => addDown p a.n)
    (addDownPre p t S) (addDownPost p t S) (fun a => a.n.toNat) ?_ a
  intro a smaller
  have hsum := sumDown_ge a.n.toNat
  have hzero : a.n = 0#32 →
      BitVec.ofNat 64 (a.value.toNat + sumDown a.n.toNat) = a.value := by
    intro hn
    simp [hn, sumDown]
  simp only [addDownPre] at *
  fsym
  all_goals first
    | apply addDown_bound_step <;> assumption
    | apply EUpd.of_imp
      intro r hr
      apply of_eq ?_ hr
      dsimp [addDownPost]
      rw [sep_left_comm_eq (sp t S a.depth) (up (pts p 8 (_ : BitVec 64))) unmetered,
        sep_left_comm_eq (cur t) (up (pts p 8 (_ : BitVec 64))) (sp t S a.depth ⋆ unmetered)]
      apply congrArg (fun v : BitVec 64 => up (pts p 8 v) ⋆
        (cur t ⋆ (sp t S a.depth ⋆ unmetered)))
      apply congrArg (BitVec.ofNat 64)
      apply addDown_sum_step <;> assumption

/-- `addDown` preserves the current thread and its original stack depth, updates exactly the
owned accumulator, and preserves its unmetered execution mode. The room includes the base
invocation's frame; no native stack or AIR correspondence claim follows from this model proof. -/
theorem addDown_total (p : Ptr) (n : BitVec 32) (x : BitVec 64) (t S D : Nat) :
    FTotalTriple
      (⟪x.toNat + sumDown n.toNat < 2 ^ 64 ∧ D + frameBase * (n.toNat + 1) ≤ S⟫ ⋆
        (up (pts p 8 x) ⋆ (cur t ⋆ (sp t S D ⋆ unmetered))))
      (addDown p n)
      (fun _ => up (pts p 8 (BitVec.ofNat 64 (x.toNat + sumDown n.toNat))) ⋆
        (cur t ⋆ (sp t S D ⋆ unmetered))) :=
  addDown_group p t S ⟨n, x, D⟩

/-- One writable zero-valued global and a real 32-byte main-thread reserve admit `addDown 1`.
The global's remaining address/extent knowledge is kept in the witness's frame. -/
private theorem addDown_budget_pre :
    Witness.FAdmit (addDownPre ⟨some 0, 0⟩ 0 32 ⟨1#32, 0#64, 0⟩) := by
  let gs : List (Array Byte × Nat × BlockKind) := [(Enc.encode (0#64), 8, .global)]
  have hfit : Mem.GlobalsFit gs := by decide +kernel
  have hr : ((Mem.ofGlobals default gs).reserveAt? 0 32).isSome := by decide +kernel
  obtain ⟨hh, hg⟩ := initRes_holds_stack default gs (by simp [gs, BlockKind.mappedLo]) 32 hr
  have bytes := fun (r : Res) (h : globals gs r) =>
    globals_pts (gs := gs) (j := 0) (bs := Enc.encode (0#64)) (a := 8) (K := .global)
      (v := 0#64) (by rfl) (LawfulEnc.size_encode _) (LawfulEnc.decode_encode _)
      (by decide) (by decide) h
  have hp := sep_mono_left bytes hg
  have hs := sep_assoc' (sep_mono_right (fun _ h => sep_comm h) (sep_assoc hp))
  apply Witness.FAdmit.mono (P := up (pts ⟨some 0, 0⟩ 8 (0#64)) ⋆ stackStart 32)
  · apply Witness.FAdmit.frame
    exact ⟨_, _, _, hh, hs, (Mem.init_fseq default gs hfit).withStack 32, trivial⟩
  · exact fun _ ha => sep_lift.mpr ⟨by decide, ha⟩

nonvacuity_witness addDown_total := ⟨⟨some 0, 0⟩, 1, 0, 0, 32, 0, addDown_budget_pre⟩

/-! ## Non-vacuity witnesses: two `u32` one after the other in one block -/

/-- `0` at `p0` and `1` at `p0 + 4`. -/
theorem swap_pre : Witness.FAdmit (up (pts Witness.p0 4 (0 : BitVec 32)) ⋆
    up (pts (Witness.p0.add 4) 4 (1 : BitVec 32))) :=
  (Witness.FAdmit.up (Witness.mem1_pts₂ (0 : BitVec 32) (1 : BitVec 32) (by decide) (by decide +kernel))
    (Witness.mem1_fseq _ _ (by decide +kernel))).mono fun _ h => up_sep h

theorem swap_self_pre : Witness.FAdmit (up (pts Witness.p0 4 (0 : BitVec 32))) :=
  Witness.FAdmit.up Witness.pts32 (Witness.mem1_fseq _ _ (by decide +kernel))

-- Total triples: the return is part of the claim, so they need no liveness witness.
nonvacuity_witness swap_sep := ⟨Witness.p0, Witness.p0.add 4, 0, 1, swap_pre⟩
nonvacuity_witness swap_self_sep := ⟨Witness.p0, 0, swap_self_pre⟩
