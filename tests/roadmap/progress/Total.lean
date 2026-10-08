import ZigLean.Conc.Total

open Zig Zig.Conc.Total

-- Positive family, not finite-fuel sampling: every finite backoff count completes
-- for every oracle, and every budget above the proved decreasing-measure bound.
example (n fuel : Nat) (o : Nat → Nat) (h : n ≤ fuel) :
    (Sched.run (fun _ => pure ()) fuel o (countdown n) {}).run =
      some (.ok ((), ({} : Mem))) := countdown_run n fuel o h

example (n : Nat) :
    EventuallyReturns (fun _ => pure ()) (countdown n) {} (fun _ m => m = {}) :=
  countdown_total n

-- A hint is still a genuine sync operation. Removing it makes this oracle fail;
-- a zero budget does not constitute a successful result.
example : (countdown 1) 0 {} = .leaf none := rfl

private def twoReady (step : Nat) : Sched.State Unit Unit :=
  { main := .paused ⟨0, .yield, fun _ m => .leaf (some (.ok ((), m)))⟩
    kids := #[.paused ⟨0, .yield, fun _ m => .leaf (some (.ok ((), m)))⟩]
    mem := {}, step := step, trace := #[] }

-- Negative scheduler-premise oracle: with both tasks ready, the legal constant-zero
-- oracle always selects main, at every choice index. Readiness alone does not imply
-- a scheduling opportunity for the child. This is a choice-level counterexample,
-- not a claim that the finite countdown above diverges.
private theorem twoReady_ready (step : Nat) : (twoReady step).ready = #[0, 1] := rfl

example (step : Nat) : (twoReady step).ready = #[0, 1] := twoReady_ready step

example (step : Nat) :
    ((twoReady step).choose (fun _ => 0) (twoReady step).ready.size).1 = 0 := rfl

example : ¬ (∀ t ∈ (twoReady 0).ready.toList, ∃ step,
    ((twoReady step).choose (fun _ => 0) (twoReady step).ready.size).1 = t) := by
  intro h
  obtain ⟨step, hs⟩ := h 1 (by rw [twoReady_ready]; simp)
  have hz : ((twoReady step).choose (fun _ => 0) (twoReady step).ready.size).1 = 0 := rfl
  rw [hz] at hs
  omega

-- P05 bounded and conditional interfaces. The bound is uniform in the oracle.
example (n : Nat) :
    ReturnsWithin n (fun _ => pure ()) (countdown n) {} (fun _ m => m = {}) :=
  countdown_within n

-- An unconditional result holds under any premise; the conditional form needs the premise
-- for every oracle before it yields the unconditional one.
example (n : Nat) (Fair : (Nat → Nat) → Prop) :
    EventuallyReturnsUnder Fair (fun _ => pure ()) (countdown n) {} (fun _ m => m = {}) :=
  (countdown_total n).under Fair

-- Vacuity: an unsatisfiable premise "proves" return for a program that never returns,
-- which has neither unconditional form.
example : EventuallyReturnsUnder (fun _ => False) (fun (_ : Unit) => pure ())
    (stuck : ConcM Unit Unit) {} (fun _ _ => False) := under_false
example : ¬ EventuallyReturns (fun (_ : Unit) => pure ()) (stuck : ConcM Unit Unit) {}
    (fun _ _ => True) := stuck_not_eventuallyReturns _ _ _
example (B : Nat) : ¬ ReturnsWithin B (fun (_ : Unit) => pure ()) (stuck : ConcM Unit Unit) {}
    (fun _ _ => True) := stuck_not_returnsWithin B _ _ _
