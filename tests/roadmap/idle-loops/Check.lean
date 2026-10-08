import IdleLoop.Theorems

/-! Kernel-checked C03 idle-loop contracts: the statements, and the axioms they use. -/

open Zig IdleLoop.Client

-- Safety: every oracle and fuel; no error (no panic, race or deadlock). No result is allowed.
example (fuel : Nat) (o : Nat → Nat) (e : Error) :
    (Sched.run dispatch fuel o main mem0).run ≠ some (.error e) := idle_safe fuel o e

-- Progress needs the explicit premise `Cooperative` (THR-09).
example (o : Nat → Nat) (h : Cooperative o) : ∃ bound, ∀ fuel, bound ≤ fuel →
    ∃ M, (Sched.run dispatch fuel o main mem0).run = some (.ok ((), M)) := idle_progress o h

-- A legal oracle under which the worker spins and yields forever; it is not cooperative.
example (fuel : Nat) : (Sched.run dispatch fuel favorWorker main mem0).run = none :=
  idle_starves fuel
example : ¬ Cooperative favorWorker := favorWorker_not_cooperative
example : Cooperative (fun _ => 0) := zero_cooperative
example : ¬ ∀ o : Nat → Nat, ∃ bound, ∀ fuel, bound ≤ fuel →
    ∃ M, (Sched.run dispatch fuel o main mem0).run = some (.ok ((), M)) := progress_needs_premise
example : ¬ Zig.Conc.Total.EventuallyReturns dispatch main mem0 (fun _ _ => True) :=
  not_eventuallyReturns

-- P05 conditional concurrent termination: the premise is an explicit argument of the interface.
example : Zig.Conc.Total.EventuallyReturnsUnder Cooperative dispatch main mem0 (fun _ _ => True) :=
  idle_total_under
example : ¬ ∀ o, Cooperative o := cooperative_not_all

-- The worker runs the translated loop: one iteration is a load, then hint and yield on 0.
example : worker = wLoop := worker_eq

-- Only the standard axioms: no `sorry`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'IdleLoop.Client.idle_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_safe

/-- info: 'IdleLoop.Client.idle_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_progress

/-- info: 'IdleLoop.Client.idle_starves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_starves

/-- info: 'IdleLoop.Client.progress_needs_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms progress_needs_premise

/-- info: 'IdleLoop.Client.idle_total_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_total_under
