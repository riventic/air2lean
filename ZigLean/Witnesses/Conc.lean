import ZigLean.Conc.Witness
import ZigLean.Conc.Total
import ZigLean.Conc.Word
import ZigLean.Conc.WeakCasLemmas
import ZigLean.Conc.TimedCompare

/-!
# Non-vacuity and liveness witnesses: concurrency rules and protocol lemmas

Concrete arguments, an admissible memory and (for a thread triple) a returning run for the
lemmas of `ZigLean/Conc/*.lean` (`docs/claim-strength.md`). A thread triple's input owns its
precondition because the memory has an empty footprint (`TAdmit.mem1`).
-/

namespace Zig.Witness

open Assn Conc

/-- The four owned bytes of `mem1 w32`. -/
theorem tbytes32 : bytesAt p0 4096 4 .heap (Enc.encode (0 : BitVec 32))
    (mem1 (Enc.encode (0 : BitVec 32))).heap :=
  mem1_bytesAt' (LawfulEnc.size_encode _)

/-! ## Thread triples (`ZigLean/Conc/Own.lean`) -/

nonvacuity_witness TTriple.ret := ⟨Unit, fun _ => emp, (), TAdmit.of_empty rfl⟩
liveness_witness TTriple.ret := ⟨Unit, fun _ => emp, (), TLive.of_empty rfl ⟨_, rfl⟩⟩

theorem ret_run : ∀ (m : Mem) (hP hF : Heap), hP.Disjoint hF → m.heap = hP ∪ hF → emp hP →
    m.current < m.clocks.size → m.Owns m.current hP →
    ∃ (v : Unit) (m' : Mem) (hQ : Heap), (pure () : MemM Unit).run m = pure (v, m') ∧
      hQ.Disjoint hF ∧ m'.heap = hQ ∪ hF ∧ emp hQ ∧ m'.Owns m'.current hQ ∧ StepIn hF m m' :=
  fun m hP _ hd hm hq _ ho => ⟨(), m, hP, rfl, hd, hm, hq, ho, StepIn.refl m _⟩

nonvacuity_witness TTriple.of_run := ⟨Unit, emp, fun _ => emp, pure (), ret_run, TAdmit.of_empty rfl⟩
liveness_witness TTriple.of_run :=
  ⟨Unit, emp, fun _ => emp, pure (), ret_run, TLive.of_empty rfl ⟨_, rfl⟩⟩

nonvacuity_witness TTriple.load :=
  ⟨BitVec 32, inferInstance, p0, 4, 0, by decide +kernel, TAdmit.mem1 pts32⟩
liveness_witness TTriple.load :=
  ⟨BitVec 32, inferInstance, p0, 4, 0, by decide +kernel,
    TLive.mem1 pts32 (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.store :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, 4, 0, by decide +kernel, 1, TAdmit.mem1 pts32⟩
liveness_witness TTriple.store :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, 4, 0, by decide +kernel, 1,
    TLive.mem1 pts32 (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.loadAt :=
  ⟨BitVec 32, inferInstance, p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32), 0, 4, 0, rfl,
    by decide +kernel, by decide +kernel, by decide, by with_unfolding_all rfl, TAdmit.mem1 tbytes32⟩
liveness_witness TTriple.loadAt :=
  ⟨BitVec 32, inferInstance, p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32), 0, 4, 0, rfl,
    by decide +kernel, by decide +kernel, by decide, by with_unfolding_all rfl,
    TLive.mem1 tbytes32 (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.storeAt :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32),
    0, 4, 1, rfl, by decide +kernel, by decide +kernel, by decide, by decide, TAdmit.mem1 tbytes32⟩
liveness_witness TTriple.storeAt :=
  ⟨BitVec 32, inferInstance, inferInstance, p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32),
    0, 4, 1, rfl, by decide +kernel, by decide +kernel, by decide, by decide,
    TLive.mem1 tbytes32 (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.storeAt' :=
  ⟨BitVec 32, inferInstance, p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32), 0, 4, 1,
    LawfulEnc.size_encode _, rfl, by decide +kernel, by decide +kernel, by decide, by decide,
    TAdmit.mem1 tbytes32⟩
liveness_witness TTriple.storeAt' :=
  ⟨BitVec 32, inferInstance, p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32), 0, 4, 1,
    LawfulEnc.size_encode _, rfl, by decide +kernel, by decide +kernel, by decide, by decide,
    TLive.mem1 tbytes32 (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.storeBytesAt :=
  ⟨p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32), 0, 4, Enc.encode (1 : BitVec 32), rfl,
    by decide +kernel, by decide +kernel, by decide, by decide, TAdmit.mem1 tbytes32⟩
liveness_witness TTriple.storeBytesAt :=
  ⟨p0, p0.add 0, 4096, 4, .heap, Enc.encode (0 : BitVec 32), 0, 4, Enc.encode (1 : BitVec 32), rfl,
    by decide +kernel, by decide +kernel, by decide, by decide,
    TLive.mem1 tbytes32 (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.alloc := ⟨.stack, 1, 1, by decide, TAdmit.of_empty rfl⟩
liveness_witness TTriple.alloc :=
  ⟨.stack, 1, 1, by decide, TLive.of_empty rfl (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness alloc_next := ⟨emp, 1, 1, by decide, TAdmit.of_empty rfl⟩
liveness_witness alloc_next := ⟨emp, 1, 1, by decide, TLive.of_empty rfl (ok_of_okb (by decide +kernel))⟩

nonvacuity_witness TTriple.free := ⟨p0, 4096, 1, .heap, #[.undef], rfl, rfl, by decide, TAdmit.mem1 (byte1 .heap)⟩
liveness_witness TTriple.free :=
  ⟨p0, 4096, 1, .heap, #[.undef], rfl, rfl, by decide,
    TLive.mem1 (byte1 .heap) (ok_of_okb (by decide +kernel))⟩

/-! ## Protocol lemmas (`ZigLean/Conc/Lemmas.lean`, `ZigLean/Conc/Logic.lean`, …) -/

nonvacuity_witness Proto.access_pure :=
  ⟨mem1 (Enc.encode (0 : BitVec 32)), p0, 4, 4, (0, blk (Enc.encode (0 : BitVec 32)), 0),
    by with_unfolding_all rfl, trivial⟩

nonvacuity_witness Proto.casMarkWrite_run :=
  ⟨32, 4, p0, mem1 (Enc.encode (0 : BitVec 32)), 0, 0, blk (Enc.encode (0 : BitVec 32)),
    by with_unfolding_all rfl, mem1_noRace _ _ _ _ _ _, trivial⟩

nonvacuity_witness Proto.futexWait_run_go :=
  ⟨p0, 0, mem1 (Enc.encode (0 : BitVec 32)), 0, blk (Enc.encode (0 : BitVec 32)), 0, 0, by decide +kernel,
    by with_unfolding_all rfl, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness Proto.futexWait_run_woken := ⟨p0, 0, { woken := #[0] }, by decide +kernel, trivial⟩

nonvacuity_witness Proto.intOfBytes_rmw := ⟨32, inferInstance, 0, trivial⟩

nonvacuity_witness Proto.checkJoined_of := ⟨0, {}, by simp [Proto.joinedAll], trivial⟩

nonvacuity_witness Proto.weakCasPrep_of :=
  ⟨32, 4, _, p0, 0, mem1 (Enc.encode (0 : BitVec 32)), _, _, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness TimedBody.selectedMessage_currentValue :=
  ⟨Enc.encode (0 : BitVec 32), Enc.encode (0 : BitVec 32), 0, rfl, by with_unfolding_all rfl, trivial⟩

nonvacuity_witness Total.countdown_run := ⟨0, 0, fun _ => 0, Nat.le_refl 0, trivial⟩
nonvacuity_witness Total.go_countdown :=
  ⟨0, 0, 1, 0, #[], fun _ => 0, Nat.le_refl 0, Nat.le_refl 1, trivial⟩

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
