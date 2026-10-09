import ZigLean.Conc.Progress

/-!
# A finite progress client

This first slice covers a single ready task with a finite number of scheduling hints.
There is no retry, shared-memory polling, fork, or blocking operation. Hence scheduling
and memory progress are structural: the ready set is a singleton and a hint cannot
fail. No fairness axiom is added to the existing safety logic.

The proof below inducts on remaining hints and follows `Sched.go`'s actual turn rule.
It quantifies over every oracle and every sufficiently large fuel; finite testing is
not used to justify termination. Fork/join and weak-CAS retry liveness remain separate.
-/

namespace Zig.Conc.Total

open Zig

/-- Total correctness requires a successful result for every sufficiently large budget.
The bound may depend on the scheduling oracle; safety is a separate all-fuel property. -/
def EventuallyReturns {Tgt α : Type} (env : Env) (dispatch : Tgt → ConcM Tgt Unit)
    (main : ConcM Tgt α) (m : Mem) (Q : α → Mem → Prop) : Prop :=
  ∀ o, ∃ bound, ∀ fuel, bound ≤ fuel →
    ∃ v m', (Sched.run env dispatch fuel o main m).run = some (.ok (v, m')) ∧ Q v m'

/-- A useful bounded backoff fragment: expose `n` scheduling opportunities and return.
Unlike a polling/retry loop, this always decreases its remaining-work measure. -/
def countdown : Nat → ConcM Unit Unit
  | 0 => pure ()
  | n + 1 => do
    spinLoopHint
    countdown n

private theorem countdown_zero_eval (depth : Nat) (m : Mem) :
    countdown 0 depth m = .leaf (some (.ok ((), m))) := rfl

private theorem countdown_succ_eval (n depth : Nat) (m : Mem) :
    countdown (n + 1) (depth + 1) m =
      .sync .yield m (fun _ m' => countdown n depth m') := rfl

private def pending (n depth step : Nat) (trace : Array Nat) : Sched.State Unit Unit :=
  { main := .paused ⟨depth, .yield, fun _ m => countdown n depth m⟩
    kids := #[], mem := {}, step := step, trace := trace }

private theorem pending_ready (n depth step : Nat) (trace : Array Nat) :
    (pending n depth step trace).ready = #[0] := rfl

private theorem singleton_choice (choice : Nat) :
    ([0] : List Nat)[choice]?.getD 0 = 0 := by
  cases choice <;> rfl

private theorem joined_empty : Conc.Proto.joinedAll 0 ({} : Mem) := by
  simp [Conc.Proto.joinedAll]

/-- Each scheduler turn consumes one hint. The induction measure is the remaining
hint count, independently of the numerical values returned by the oracle. -/
private theorem go_countdown (env : Env) (n : Nat) :
    ∀ depth fuel step trace (o : Nat → Nat), n ≤ depth → n + 1 ≤ fuel →
      (Sched.go env (fun _ => pure ()) o fuel (pending n depth step trace)).1 =
        some (.ok ((), ({} : Mem))) := by
  induction n with
  | zero =>
    intro depth fuel step trace o hd hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [Sched.go, pending_ready]
      simp [pending, Sched.State.choose, Sched.turnTrace, Sched.settle,
        countdown_zero_eval, singleton_choice, Conc.Proto.checkJoined_of joined_empty]
  | succ n ih =>
    intro depth fuel step trace o hd hf
    cases depth with
    | zero => omega
    | succ depth =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [Sched.go, pending_ready]
        simpa [pending, Sched.State.choose, Sched.turnTrace, Sched.settle,
          countdown_succ_eval, singleton_choice]
          using ih depth fuel (step + 1) (trace.push 1) o (by omega) (by omega)

/-- Completion of bounded backoff, for every oracle and all sufficient fuel.
The explicit bound follows the decreasing hint count, not an eventual-result premise. -/
theorem countdown_run (env : Env) (n fuel : Nat) (o : Nat → Nat) (hf : n ≤ fuel) :
    (Sched.run env (fun _ => pure ()) fuel o (countdown n) {}).run =
      some (.ok ((), ({} : Mem))) := by
  cases n with
  | zero =>
    simp [Sched.run, Sched.runTrace, Sched.settle, countdown_zero_eval,
      Conc.Proto.checkJoined_of joined_empty]
  | succ n =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simpa [Sched.run, Sched.runTrace, Sched.settle, countdown_succ_eval, pending]
        using go_countdown env n fuel (fuel + 1) 0 #[] o (by omega) (by omega)

theorem countdown_total (env : Env) (n : Nat) :
    EventuallyReturns env (fun _ => pure ()) (countdown n) {} (fun _ m => m = {}) := by
  intro o
  exact ⟨n, fun fuel hf => ⟨(), {}, countdown_run env n fuel o hf, rfl⟩⟩

end Zig.Conc.Total
