import ZigLean.Sep.Triple

/-!
Outcome-taxonomy fixtures (V06). The contract type keeps a Zig error return apart from a model
panic: `E!T` is a returned `Except ErrName T` value, while `Zig.Error` constructors are safety
failures. A partial triple therefore holds for an error return and fails for every model
failure class (panic, illegal behavior, unspecified behavior including the no-clock timer
path, deadlock). Divergence satisfies it vacuously, so it is not a guaranteed-return claim.
-/

open Zig Assn

namespace OutcomeTaxonomy

/-- A Zig error return (`error.Timeout`) is an ordinary returned value. -/
def errorReturn : MemM (Except ErrName Nat) := pure (.error "Timeout")

theorem errorReturn_triple (P : Assn) :
    Triple P errorReturn (fun r => fun h => r = .error "Timeout" ∧ P h) := by
  intro m hP hF hd hm hp hs
  exact ⟨hP, hd, hm, ⟨rfl, hp⟩, hs⟩

/-- Any model failure constructor. The timer model reports `.unspecified` (TMR-01). -/
def fail (e : Error) : MemM Nat := throw e

/-- No partial triple holds for a model failure on any admissible input. -/
theorem fail_not_triple (e : Error) (P : Assn) (Q : Nat → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ Triple P (fail e) Q := by
  intro ht
  exact ht m hP hF hd hm hp hs

theorem panic_not_triple (P : Assn) (Q : Nat → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ Triple P (fail .panic) Q := fail_not_triple .panic P Q m hP hF hd hm hp hs

theorem unspecified_not_triple (P : Assn) (Q : Nat → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ Triple P (fail .unspecified) Q := fail_not_triple .unspecified P Q m hP hF hd hm hp hs

theorem illegal_not_triple (P : Assn) (Q : Nat → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ Triple P (fail .illegal) Q := fail_not_triple .illegal P Q m hP hF hd hm hp hs

theorem deadlock_not_triple (P : Assn) (Q : Nat → Assn) (m : Mem) (hP hF : Heap)
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) :
    ¬ Triple P (fail .deadlock) Q := fail_not_triple .deadlock P Q m hP hF hd hm hp hs

/-- Divergence (`none`) satisfies a partial triple with a false postcondition. -/
def diverge : MemM Nat := fun _ => ExceptT.mk none

theorem diverge_triple (P : Assn) : Triple P diverge (fun _ _ => False) := by
  intro m hP hF hd hm hp hs
  trivial

/-- The model failure classes stay distinct constructors. -/
example : Error.unspecified ≠ Error.panic := by decide
example : Error.illegal ≠ Error.unspecified := by decide
example : Error.deadlock ≠ Error.panic := by decide

end OutcomeTaxonomy
