import ZigLean.Conc.Unroll
import ZigLean.Sep.Full.Unroll
import Proofs.Threads.Gen

open Zig Threads

/-! `unroll_sched`: a concrete run of a program with loops, by the kernel. -/

-- `parallelCounter 5`: `main` spawns 4 threads (5 runs of its spawn loop's body) that each
-- increment 5 times (6 runs of the body: 5 repeats and the exit); the kernel computes the run
-- with each loop cut after 6 iterations.
theorem counter_completes :
    Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 20 := by
  unroll_sched 6

-- No `native_decide`: only the standard axioms.
/-- info: 'counter_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms counter_completes

-- Rejected: a wrong result.
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 6 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 21 := by
  unroll_sched 6

-- Rejected: the increment loop needs 6 iterations; cut after 5 the run has no result.
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 5 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 20 := by
  unroll_sched 5

-- Rejected: out of fuel (each thread's turns count).
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 6 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 5 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 20 := by
  unroll_sched 6

-- Rejected: a goal without a run of the scheduler.
/-- error: unroll_sched: the goal has no `Sched.run env dispatch fuel o main m₀` -/
#guard_msgs in
example : (1 : Nat) = 1 := by
  unroll_sched 4

-- The cut loop is below the loop, so its result is the loop's result.
example {σ ε : Type} (body : M σ ε) (again : ε → Bool) (k : Nat) :
    Lean.Order.PartialOrder.rel (loopN body again k) (loop body again) :=
  loopN_le_loop body again k

/-! A `partial_fixpoint` group (as a recursive call group of generated code): `unroll_sched`
cuts its fixpoint after `k` unfoldings (`fixSel`, `fixN_le_fix`). -/

mutual
def evenC (n : Nat) : ConcM Unit (Except ErrName (BitVec 32)) :=
  if n = 0 then pure (.ok 1) else oddC (n - 1)
partial_fixpoint
def oddC (n : Nat) : ConcM Unit (Except ErrName (BitVec 32)) :=
  if n = 0 then pure (.ok 0) else evenC (n - 1)
partial_fixpoint
end

theorem even_six : Witness.okVal (Sched.run ⟨.any, .available⟩ (fun _ => pure ()) 100 (fun _ => 0)
    (evenC 6) {}) = some 1 := by
  unroll_sched 8

/-- info: 'even_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms even_six

-- Rejected: the group needs 7 unfoldings; cut after 3 the run has no result.
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 3 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run ⟨.any, .available⟩ (fun _ => pure ()) 100 (fun _ => 0)
    (evenC 6) {}) = some 1 := by
  unroll_sched 3

-- Any observation of the run: its error (`Witness.errOf`).
theorem odd_zero_fails : Witness.errOf (Sched.run ⟨.any, .available⟩ (fun _ => pure ()) 100 (fun _ => 0)
    (do let _ ← evenC 3; (throw .panic : ConcM Unit Unit)) {}) = some .panic := by
  unroll_sched 5

-- Rejected: `none` is also the observation of a run without a result.
/-- error: unroll_sched: the goal's value is also the value of a run without a result -/
#guard_msgs in
example : Witness.errOf (Sched.run ⟨.any, .available⟩ (fun _ => pure ()) 100 (fun _ => 0)
    (evenC 6) {}) = none := by
  unroll_sched 8

/-! `unroll_solo`: the in-thread reading (`Sched.soloRun`) that `CTriple` speaks about. -/

theorem even_six_solo : Witness.okVal ((Sched.soloRun 100 (evenC 6)).run {}) = some 1 := by
  unroll_solo 8

/-- info: 'even_six_solo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms even_six_solo

/-- error: unroll_solo: the kernel does not compute the run with loops cut after 3 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal ((Sched.soloRun 100 (evenC 6)).run {}) = some 1 := by
  unroll_solo 3
