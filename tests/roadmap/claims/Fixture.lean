import ZigLean.Sep.Total

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

end ClaimFixture
