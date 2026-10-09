import ZigLean.Conc.Unroll
import Proofs.Threads.Gen

open Zig Threads

/-! `unroll_sched`: a concrete run of a program with loops, by the kernel. -/

-- `parallelCounter 5`: `main` spawns 4 threads (5 runs of its spawn loop's body) that each
-- increment 5 times (6 runs of the body: 5 repeats and the exit); the kernel computes the run
-- with each loop cut after 6 iterations.
theorem counter_completes :
    Witness.okVal (Sched.run dispatch 1000 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 20 := by
  unroll_sched 6

-- No `native_decide`: only the standard axioms.
/-- info: 'counter_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms counter_completes

-- Rejected: a wrong result.
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 6 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run dispatch 1000 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 21 := by
  unroll_sched 6

-- Rejected: the increment loop needs 6 iterations; cut after 5 the run has no result.
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 5 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run dispatch 1000 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 20 := by
  unroll_sched 5

-- Rejected: out of fuel (each thread's turns count).
/-- error: unroll_sched: the kernel does not compute the run with loops cut after 6 iterations to the goal's value (another result or error, out of fuel, or a loop that needs more iterations) -/
#guard_msgs (whitespace := lax) in
example : Witness.okVal (Sched.run dispatch 5 (fun _ => 0) (parallelCounter 5) (mem0 .fresh)) = some 20 := by
  unroll_sched 6

-- Rejected: a goal without a run of the scheduler.
/-- error: unroll_sched: the goal has no `Sched.run dispatch fuel o main m₀` -/
#guard_msgs in
example : (1 : Nat) = 1 := by
  unroll_sched 4

-- The cut loop is below the loop, so its result is the loop's result.
example {σ ε : Type} (body : M σ ε) (again : ε → Bool) (k : Nat) :
    Lean.Order.PartialOrder.rel (loopN body again k) (loop body again) :=
  loopN_le_loop body again k
