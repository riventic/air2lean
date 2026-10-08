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

Three return interfaces, from strongest to weakest:

* `ReturnsWithin B`: every oracle returns once the budget is at least `B` turns (uniform bound).
* `EventuallyReturns`: every oracle returns for every large enough budget (oracle-dependent).
* `EventuallyReturnsUnder Fair`: only oracles satisfying the explicit premise `Fair` return.
  The premise is part of the statement, never an implicit axiom; `under_false` shows that an
  unsatisfiable premise makes it vacuous, so it cannot stand in for the unconditional forms.
-/

namespace Zig.Conc.Total

open Zig

/-- Total correctness requires a successful result for every sufficiently large budget.
The bound may depend on the scheduling oracle; safety is a separate all-fuel property. -/
def EventuallyReturns {Tgt α : Type} (dispatch : Tgt → ConcM Tgt Unit)
    (main : ConcM Tgt α) (m : Mem) (Q : α → Mem → Prop) : Prop :=
  ∀ o, ∃ bound, ∀ fuel, bound ≤ fuel →
    ∃ v m', (Sched.run dispatch fuel o main m).run = some (.ok (v, m')) ∧ Q v m'

/-- Bounded concurrent total correctness: under every oracle, every budget of at least `B`
scheduler turns gives a successful result. The bound is uniform in the oracle. -/
def ReturnsWithin {Tgt α : Type} (B : Nat) (dispatch : Tgt → ConcM Tgt Unit)
    (main : ConcM Tgt α) (m : Mem) (Q : α → Mem → Prop) : Prop :=
  ∀ o fuel, B ≤ fuel →
    ∃ v m', (Sched.run dispatch fuel o main m).run = some (.ok (v, m')) ∧ Q v m'

/-- Guaranteed return under an explicit schedule premise `Fair`: every oracle that satisfies
`Fair` eventually returns. This is weaker than `EventuallyReturns`: it says nothing about
oracles outside `Fair`, and an unsatisfiable `Fair` makes it vacuous (`under_false`). -/
def EventuallyReturnsUnder {Tgt α : Type} (Fair : (Nat → Nat) → Prop)
    (dispatch : Tgt → ConcM Tgt Unit) (main : ConcM Tgt α) (m : Mem) (Q : α → Mem → Prop) :
    Prop :=
  ∀ o, Fair o → ∃ bound, ∀ fuel, bound ≤ fuel →
    ∃ v m', (Sched.run dispatch fuel o main m).run = some (.ok (v, m')) ∧ Q v m'

section Interfaces

variable {Tgt α : Type} {dispatch : Tgt → ConcM Tgt Unit} {main : ConcM Tgt α} {m : Mem}
  {Q Q' : α → Mem → Prop} {Fair Fair' : (Nat → Nat) → Prop} {B B' : Nat}

theorem ReturnsWithin.eventually (h : ReturnsWithin B dispatch main m Q) :
    EventuallyReturns dispatch main m Q := fun o => ⟨B, h o⟩

theorem ReturnsWithin.mono (h : ReturnsWithin B dispatch main m Q) (hB : B ≤ B') :
    ReturnsWithin B' dispatch main m Q := fun o fuel hf => h o fuel (Nat.le_trans hB hf)

theorem EventuallyReturns.conseq (h : EventuallyReturns dispatch main m Q)
    (hq : ∀ v m', Q v m' → Q' v m') : EventuallyReturns dispatch main m Q' := by
  intro o
  obtain ⟨b, hb⟩ := h o
  refine ⟨b, fun fuel hf => ?_⟩
  obtain ⟨v, m', hr, hv⟩ := hb fuel hf
  exact ⟨v, m', hr, hq _ _ hv⟩

/-- An unconditional result holds under any premise. -/
theorem EventuallyReturns.under (h : EventuallyReturns dispatch main m Q)
    (Fair : (Nat → Nat) → Prop) : EventuallyReturnsUnder Fair dispatch main m Q :=
  fun o _ => h o

/-- The conditional form with the trivial premise is the unconditional one. -/
theorem eventuallyReturnsUnder_true :
    EventuallyReturnsUnder (fun _ => True) dispatch main m Q ↔
      EventuallyReturns dispatch main m Q :=
  ⟨fun h o => h o trivial, fun h => h.under _⟩

/-- Discharging the premise for every oracle gives the unconditional form. -/
theorem EventuallyReturnsUnder.discharge (h : EventuallyReturnsUnder Fair dispatch main m Q)
    (hall : ∀ o, Fair o) : EventuallyReturns dispatch main m Q := fun o => h o (hall o)

/-- A stronger premise gives a weaker statement. -/
theorem EventuallyReturnsUnder.mono (h : EventuallyReturnsUnder Fair dispatch main m Q)
    (hF : ∀ o, Fair' o → Fair o) : EventuallyReturnsUnder Fair' dispatch main m Q :=
  fun o ho => h o (hF o ho)

theorem EventuallyReturnsUnder.conseq (h : EventuallyReturnsUnder Fair dispatch main m Q)
    (hq : ∀ v m', Q v m' → Q' v m') : EventuallyReturnsUnder Fair dispatch main m Q' := by
  intro o ho
  obtain ⟨b, hb⟩ := h o ho
  refine ⟨b, fun fuel hf => ?_⟩
  obtain ⟨v, m', hr, hv⟩ := hb fuel hf
  exact ⟨v, m', hr, hq _ _ hv⟩

/-- Vacuity: an unsatisfiable premise proves any conditional result, even a false
postcondition for a program that never returns. Hence the conditional form can never stand
in for `EventuallyReturns`. -/
theorem under_false : EventuallyReturnsUnder (fun _ => False) dispatch main m Q :=
  fun _ h => h.elim

end Interfaces

/-- A program that never returns: its first step has no result. -/
def stuck {Tgt α : Type} : ConcM Tgt α := fun _ _ => .leaf none

theorem stuck_run {Tgt α : Type} (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat)
    (m : Mem) : (Sched.run dispatch fuel o (stuck : ConcM Tgt α) m).run = none := rfl

/-- Divergence has no unconditional or bounded guaranteed return. -/
theorem stuck_not_eventuallyReturns {Tgt α : Type} (dispatch : Tgt → ConcM Tgt Unit) (m : Mem)
    (Q : α → Mem → Prop) : ¬ EventuallyReturns dispatch (stuck : ConcM Tgt α) m Q := by
  intro h
  obtain ⟨b, hb⟩ := h (fun _ => 0)
  obtain ⟨v, m', hr, -⟩ := hb b (Nat.le_refl _)
  rw [stuck_run] at hr
  cases hr

theorem stuck_not_returnsWithin {Tgt α : Type} (B : Nat) (dispatch : Tgt → ConcM Tgt Unit)
    (m : Mem) (Q : α → Mem → Prop) : ¬ ReturnsWithin B dispatch (stuck : ConcM Tgt α) m Q :=
  fun h => stuck_not_eventuallyReturns dispatch m Q h.eventually

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
private theorem go_countdown (n : Nat) :
    ∀ depth fuel step trace (o : Nat → Nat), n ≤ depth → n + 1 ≤ fuel →
      (Sched.go (fun _ => pure ()) o fuel (pending n depth step trace)).1 =
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
theorem countdown_run (n fuel : Nat) (o : Nat → Nat) (hf : n ≤ fuel) :
    (Sched.run (fun _ => pure ()) fuel o (countdown n) {}).run =
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
        using go_countdown n fuel (fuel + 1) 0 #[] o (by omega) (by omega)

theorem countdown_total (n : Nat) :
    EventuallyReturns (fun _ => pure ()) (countdown n) {} (fun _ m => m = {}) := by
  intro o
  exact ⟨n, fun fuel hf => ⟨(), {}, countdown_run n fuel o hf, rfl⟩⟩

/-- The bound is uniform in the oracle: `n` scheduler turns suffice for `n` hints. -/
theorem countdown_within (n : Nat) :
    ReturnsWithin n (fun _ => pure ()) (countdown n) {} (fun _ m => m = {}) :=
  fun o fuel hf => ⟨(), {}, countdown_run n fuel o hf, rfl⟩

end Zig.Conc.Total
