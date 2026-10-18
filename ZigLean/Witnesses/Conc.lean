import ZigLean.Mem.Witness
import ZigLean.Conc.Total
import ZigLean.Conc.Word
import ZigLean.Conc.Base.WeakCas
import ZigLean.Conc.TimedCompare

/-!
# Non-vacuity witnesses: concurrency protocol lemmas

Concrete arguments for the premises of the lemmas of `ZigLean/Conc/*.lean`
(`docs/claim-strength.md`). The legacy thread-triple rules (`TTriple`, `ZigLean/Conc/Own.lean`)
have none: their head is a reserved claim-head name, so no claim rests on them.
-/

namespace Zig.Witness

open Conc

/-! ## Protocol lemmas (`ZigLean/Conc/Lemmas.lean`, `ZigLean/Conc/Logic.lean`, …) -/

nonvacuity_witness Proto.access_pure :=
  ⟨mem1 (Enc.encode (0 : BitVec 32)), p0, 4, 4, (0, blk (Enc.encode (0 : BitVec 32)), 0),
    by with_unfolding_all rfl, trivial⟩

nonvacuity_witness Proto.casMarkWrite_run :=
  ⟨32, 4, p0, mem1 (Enc.encode (0 : BitVec 32)), 0, 0, blk (Enc.encode (0 : BitVec 32)),
    by with_unfolding_all rfl, mem1_noRace _ _ _ _ _ _, trivial⟩

nonvacuity_witness Proto.futexWait_run_go :=
  ⟨p0, 0, mem1 (Enc.encode (0 : BitVec 32)), 0, blk (Enc.encode (0 : BitVec 32)), 0, 0, by decide +kernel,
    by with_unfolding_all rfl, mem1_noRace _ _ _ _ _ _, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness Proto.futexWait_run_woken := ⟨p0, 0, { woken := #[0] }, by decide +kernel, trivial⟩

nonvacuity_witness Proto.intOfBytes_rmw := ⟨32, inferInstance, 0, trivial⟩

nonvacuity_witness Proto.checkJoined_of := ⟨0, {}, by simp [Proto.joinedAll], trivial⟩

nonvacuity_witness Proto.weakCasPrep_of :=
  ⟨32, 4, _, p0, 0, mem1 (Enc.encode (0 : BitVec 32)), _, _, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness TimedBody.selectedMessage_currentValue :=
  ⟨Enc.encode (0 : BitVec 32), Enc.encode (0 : BitVec 32), 0, rfl, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness Total.countdown_run := ⟨⟨.any, .available⟩, 0, 0, fun _ => 0, Nat.le_refl 0, trivial⟩
nonvacuity_witness Total.go_countdown :=
  ⟨⟨.any, .available⟩, 0, 0, 1, 0, #[], fun _ => 0, Nat.le_refl 0, Nat.le_refl 1, trivial⟩

/-! ## Lock states and words (`ZigLean/Conc/LockRules.lean`, `ZigLean/Conc/Word.lean`) -/

/-- The states `0`, `1`, `3` of a `u32` mutex word. -/
def statesU32 : Lock.States (BitVec 32) where
  unl := 0
  one := 1
  two := 3
  c := 3
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

nonvacuity_witness Lock.States.dec0 := ⟨BitVec 32, inferInstance, statesU32, trivial⟩
nonvacuity_witness Lock.States.dec1 := ⟨BitVec 32, inferInstance, statesU32, trivial⟩
nonvacuity_witness Lock.States.dec2 := ⟨BitVec 32, inferInstance, statesU32, trivial⟩

nonvacuity_witness Word.enc_val := ⟨32, 4, ⟨0, 0, by decide⟩, 0, trivial⟩

end Zig.Witness
