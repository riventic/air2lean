import ZigLean.Sep.Bounded
import ZigLean.Conc.Total

/-!
Claim-strength fixtures. `scripts/claims.py` classifies each theorem from the conclusion
shape that `tools/Assurance.lean` extracts from its kernel type. No name or comment here is
read by the classifier.
-/

open Zig Assn

namespace ClaimFixture

def diverge : MemM Unit := fun _ => ExceptT.mk none

/-- Partial correctness holds vacuously for divergence, even with a false postcondition. -/
theorem diverge_partial (P : Assn) : Triple P diverge (fun _ _ => False) := by
  intro m hP hF hd hm hp hs
  trivial

/-- Vacuity guard: with any admissible input, divergence has no total triple. -/
theorem diverge_not_total (P : Assn) (Q : Unit → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTriple P diverge Q := by
  intro ht
  obtain ⟨v, m', hQ, hr, _⟩ := ht m hP hF hd hm hp hs
  change none = some (Except.ok (v, m')) at hr
  cases hr

theorem ret_total (P : Assn) (v : Nat) : TotalTriple P (pure v : MemM Nat) (fun _ => P) :=
  TotalTriple.ret (Q := fun _ => P) v

theorem ret_returns (P : Assn) (v : Nat) : Returns P (pure v : MemM Nat) :=
  (ret_total P v).returns

theorem ret_partial (P : Assn) (v : Nat) : Triple P (pure v : MemM Nat) (fun _ => P) :=
  (ret_total P v).toPartial

/-- An exact successful run is a guaranteed return with an exact result. -/
theorem ret_run (m : Mem) : (pure 7 : MemM Nat).run m = pure (7, m) := rfl

/-- An exact run that ends in a safety error is not a no-panic claim. -/
theorem panic_run (m : Mem) :
    (throw Error.panic : MemM Unit).run m = throw Error.panic := rfl

/-- The same exact successful run, stated through the result option. -/
theorem ret_some (m : Mem) :
    ((pure 7 : MemM Nat).run m).run = some (.ok (7, m)) := rfl

theorem panic_some (m : Mem) :
    ((throw Error.panic : MemM Unit).run m).run = some (.error Error.panic) := rfl

/-- `pure` in `Option` is `some`: wrapping a safety error it states a panic, not a return. -/
theorem panic_pure (m : Mem) :
    ((throw Error.panic : MemM Unit).run m).run = pure (Except.error Error.panic) := rfl

theorem ret_pure_ok (m : Mem) :
    ((pure 7 : MemM Nat).run m).run = pure (Except.ok (7, m)) := rfl

/-- Premises do not change the conclusion's head constant. -/
theorem premise_total (P : Assn) (v : Nat) (_h : 0 < v) :
    TotalTriple P (pure v : MemM Nat) (fun _ => P) := ret_total P v

/-- Definitions are not unfolded: a wrapper does not inherit total strength. -/
def Wrapped (P : Assn) (c : MemM Nat) : Prop := TotalTriple P c (fun _ => P)

theorem wrapped_total (P : Assn) (v : Nat) : Wrapped P (pure v) := ret_total P v

/-- A conjunction is not classified, even when its parts would establish total correctness. -/
theorem partial_and_returns (P : Assn) (v : Nat) :
    Triple P (pure v : MemM Nat) (fun _ => P) ∧ Returns P (pure v : MemM Nat) :=
  ⟨ret_partial P v, ret_returns P v⟩

/-! Bounded and concurrent return interfaces. -/

/-- A loop body that exits at once. -/
def exitBody : MM Unit Bool := pure false

/-- A loop body that always repeats: the loop never exits. -/
def spinBody : MM Unit Bool := pure true

/-- A bounded total triple: one body run. -/
theorem exit_within (P : Assn) : TotalTripleWithin 1 P exitBody id () (fun _ _ => P) := by
  apply TotalTripleWithin.exit
  intro m hP _ hd hm hp hs
  exact ⟨(false, ()), m, hP, rfl, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

theorem exit_within_total (P : Assn) :
    TotalTriple P ((Zig.loop exitBody id).run ()) (fun _ => P) :=
  (exit_within P).toTotal

/-- The spinning loop has no counted run. -/
theorem spin_no_run : ∀ s m k e s' m', ¬ LoopRuns spinBody id s m k e s' m' := by
  intro s m k e s' m' h
  induction h with
  | exit hb ha =>
    -- `rfl` rather than unfolding `spinBody`, which would add an equation lemma to the report.
    rw [show (spinBody.run _).run _ = pure ((true, _), _) from rfl] at hb
    simp only [pure, ExceptT.pure, ExceptT.mk] at hb
    cases hb
    simp at ha
  | next _ _ _ ih => exact ih

/-- Vacuity guard: with any admissible input, divergence has no bounded triple for any bound. -/
theorem spin_not_within (B : Nat) (P : Assn) (Q : Bool → Unit → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ TotalTripleWithin B P spinBody id () Q :=
  TotalTripleWithin.not_within_of_stuck hd hm hp hs (spin_no_run () m)

open Zig.Conc.Total in
/-- Unconditional concurrent return: every oracle, every large enough budget. -/
theorem countdown_eventually :
    EventuallyReturns (fun _ => pure ()) (countdown 2) {} (fun _ m => m = {}) :=
  countdown_total 2

open Zig.Conc.Total in
/-- Bounded concurrent return: two scheduler turns under every oracle. -/
theorem countdown_bounded :
    ReturnsWithin 2 (fun _ => pure ()) (countdown 2) {} (fun _ m => m = {}) :=
  countdown_within 2

open Zig.Conc.Total in
/-- A premise-dependent return. Its premise is unsatisfiable, so it holds even for a program
that never returns: the conditional form must not satisfy an unconditional goal. -/
theorem stuck_under_false :
    EventuallyReturnsUnder (fun _ => False) (fun (_ : Unit) => pure ()) (stuck : ConcM Unit Unit)
      {} (fun _ _ => False) :=
  under_false

open Zig.Conc.Total in
/-- A true program stated conditionally is still only a conditional claim. -/
theorem countdown_under (Fair : (Nat → Nat) → Prop) :
    EventuallyReturnsUnder Fair (fun _ => pure ()) (countdown 2) {} (fun _ m => m = {}) :=
  (countdown_total 2).under Fair

open Zig.Conc.Total in
theorem stuck_not_total :
    ¬ EventuallyReturns (fun (_ : Unit) => pure ()) (stuck : ConcM Unit Unit) {} (fun _ _ => True) :=
  stuck_not_eventuallyReturns _ _ _

end ClaimFixture
