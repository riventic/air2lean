import Proofs.Atomics.Gen
import ZigLean.Mem.Lemmas

/-!
# Proofs about `examples/atomics/atomics.zig`

The RC11 model of atomics (`ZigLean/Mem/Thread.lean`). The specs over all schedules are in
`MessagePassing.lean` (`mpRelAcq`: 0 or 42, no error), `Relaxed.lean` (`mpRelaxed`: every result
is 0) and `Stack.lean` (`stackPush`: 120 or 210, no error). This file shows that the model has the
results that only a weak memory model explains, each under a concrete schedule (an oracle), the
result of the sequentially consistent schedule (the oracle always picks option 0: the newest
message, the thread that is first), and the race of `mpRelaxed`. Each is a possibility: it holds
for some placement of the blocks (`Mem.place`), the one the kernel computes the run for
(`decide +kernel`, under `Placement.fresh`). `stackPush` has a loop, defined by
`partial_fixpoint`, which the kernel does not run.
-/

open Zig Atomics

/-- The value of a run of a function `!u32`, for a statement about it. -/
def okVal (r : Result (Except ErrName (BitVec 32) × Mem)) : Option Nat :=
  match r.run with
  | some (.ok (.ok v, _)) => some v.toNat
  | _ => none

/-- The schedule that takes the choices `cs`, then option 0. -/
def sched (cs : List Nat) : Nat → Nat := fun i => cs.getD i 0

/-- Store buffering: the sequentially consistent schedule gives `2` (the second thread reads
the first thread's write). -/
theorem sb_sc :
    ∃ σ, okVal (Sched.run dispatch 100 (sched []) sbRelaxed (mem0 σ)) = some 2 :=
  ⟨.fresh, by decide +kernel⟩

/-- Store buffering: both threads read the old value, a result of a weak memory model. -/
theorem sb_weak :
    ∃ σ, okVal (Sched.run dispatch 100 (sched [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) sbRelaxed (mem0 σ)) = some 0 :=
  ⟨.fresh, by decide +kernel⟩

/-- 2+2W: both first writes are last in the modification order, a result of a weak memory
model (`x = 1`, `y = 1`). -/
theorem twoPlusTwoW_weak :
    ∃ σ, okVal (Sched.run dispatch 100 (sched [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) twoPlusTwoW (mem0 σ)) = some 11 :=
  ⟨.fresh, by decide +kernel⟩

/-- Message passing: the reader sees the flag and then the data. -/
theorem mp_sees_data :
    ∃ σ, okVal (Sched.run dispatch 100 (sched [0, 1, 1]) mpRelAcq (mem0 σ)) = some 42 :=
  ⟨.fresh, by decide +kernel⟩

/-- The same schedule with relaxed atomics: the read of the data after the flag is a data race
(`.illegal`), since the relaxed load gives no happens-before edge. -/
theorem mpRelaxed_race :
    ∃ σ, (match (Sched.run dispatch 100 (sched [0, 1, 1]) mpRelaxed (mem0 σ)).run with
      | some (.error .illegal) => true
      | _ => false) = true :=
  ⟨.fresh, by decide +kernel⟩

namespace Zig

/-- An acquire makes the thread's clock at least the message's release clock: every write that
happened before the release write happened before the thread's later accesses, so they do not
race (`mpRelAcq`). -/
theorem acquireClock_le (c : VClock) (m : Mem) (h : m.current < m.clocks.size) :
    ∃ m', (acquireClock c).run m = pure ((), m') ∧ VClock.le c (m'.clocks[m.current]!) = true := by
  refine ⟨_, rfl, ?_⟩
  show VClock.le c ((m.clocks.set! m.current (VClock.merge (m.clocks[m.current]!) c))[m.current]!) = true
  rw [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]
  exact VClock.le_merge_right _ _

end Zig
