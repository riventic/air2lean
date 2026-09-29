import Proofs.Atomics.Gen
import ZigLean.Mem.Lemmas

/-!
# Proofs about `examples/atomics/atomics.zig`

The RC11 model of atomics (`ZigLean/Mem/Thread.lean`). A spec over all schedules is milestone T4
(`PLAN.md`); this file shows that the model has the results that only a weak memory model
explains, each under a concrete schedule (an oracle), and the result of the sequentially
consistent schedule (the oracle always picks option 0: the newest message, the thread that is
first). The kernel computes each run (`decide +kernel`); a function with a loop (`stackPush`) is
defined by `partial_fixpoint`, which the kernel does not run, so its proof waits for T4.
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
theorem sb_sc : okVal (Sched.run dispatch 100 (sched []) sbRelaxed mem0) = some 2 := by
  decide +kernel

/-- Store buffering: both threads read the old value, a result of a weak memory model. -/
theorem sb_weak :
    okVal (Sched.run dispatch 100 (sched [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) sbRelaxed mem0) =
      some 0 := by
  decide +kernel

/-- 2+2W: both first writes are last in the modification order, a result of a weak memory
model (`x = 1`, `y = 1`). -/
theorem twoPlusTwoW_weak :
    okVal (Sched.run dispatch 100 (sched [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) twoPlusTwoW mem0) =
      some 11 := by
  decide +kernel

/-- Message passing: the reader sees the flag and then the data. -/
theorem mp_sees_data :
    okVal (Sched.run dispatch 100 (sched [0, 1, 1]) mpRelAcq mem0) = some 42 := by
  decide +kernel

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
