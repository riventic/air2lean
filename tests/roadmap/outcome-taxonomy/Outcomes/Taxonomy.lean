import ZigLean.Sep.Full.Witness

/-!
Outcome-taxonomy fixtures (V06). The contract type keeps a Zig error return apart from a model
panic: `E!T` is a returned `Except ErrName T` value, while `Zig.Error` constructors are safety
failures. A partial triple (`FTriple`, `docs/sep-full-state.md`) therefore holds for an error
return and fails, on every admissible input (`Witness.FAdmit`), for every model failure class
(panic, illegal behavior, unspecified behavior, an unsupported timer (the no-clock path, its own
constructor), deadlock, an allowlisted inline-asm trap). A stack overflow is not a failure of the
program but of its stack budget (STK-01): a partial triple holds for it, as for divergence, so
neither is a guaranteed-return claim.
-/

open Zig Full FAssn Witness

namespace OutcomeTaxonomy

/-- A Zig error return (`error.Timeout`) is an ordinary returned value. -/
def errorReturn : MemM (Except ErrName Nat) := pure (.error "Timeout")

theorem errorReturn_triple (P : FAssn) :
    FTotalTriple P errorReturn (fun r => ⟪r = .error "Timeout"⟫ ⋆ P) :=
  (FTotalTriple.ret (Q := fun r : Except ErrName Nat => ⟪r = .error "Timeout"⟫ ⋆ P)
    (.error "Timeout")).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

/-- Any model failure constructor. The timed scheduler reports `.unsupportedTimer` (TMR-02). -/
def fail (e : Error) : MemM Nat := throw e

/-- No partial triple holds for a model failure on any admissible input. -/
theorem fail_not_triple (e : Error) (he : e ≠ .stackOverflow) (P : FAssn) (Q : Nat → FAssn)
    (h : FAdmit P) : ¬ FTriple P (fail e) Q := by
  intro ht
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := h
  exact he (ht m r rF hh hp hs)

theorem panic_not_triple (P : FAssn) (Q : Nat → FAssn) (h : FAdmit P) :
    ¬ FTriple P (fail .panic) Q := fail_not_triple .panic (by decide) P Q h

theorem unspecified_not_triple (P : FAssn) (Q : Nat → FAssn) (h : FAdmit P) :
    ¬ FTriple P (fail .unspecified) Q := fail_not_triple .unspecified (by decide) P Q h

theorem unsupportedTimer_not_triple (P : FAssn) (Q : Nat → FAssn) (h : FAdmit P) :
    ¬ FTriple P (fail .unsupportedTimer) Q := fail_not_triple .unsupportedTimer (by decide) P Q h

theorem illegal_not_triple (P : FAssn) (Q : Nat → FAssn) (h : FAdmit P) :
    ¬ FTriple P (fail .illegal) Q := fail_not_triple .illegal (by decide) P Q h

theorem deadlock_not_triple (P : FAssn) (Q : Nat → FAssn) (h : FAdmit P) :
    ¬ FTriple P (fail .deadlock) Q := fail_not_triple .deadlock (by decide) P Q h

theorem trap_not_triple (P : FAssn) (Q : Nat → FAssn) (h : FAdmit P) :
    ¬ FTriple P (fail .trap) Q := fail_not_triple .trap (by decide) P Q h

/-- A stack overflow satisfies a partial triple with a false postcondition (STK-01). -/
theorem stackOverflow_triple (P : FAssn) : FTriple P (fail .stackOverflow) (fun _ _ => False) :=
  fun _ _ _ _ _ _ => rfl

/-- Divergence (`none`) satisfies a partial triple with a false postcondition. -/
def diverge : MemM Nat := fun _ => ExceptT.mk none

theorem diverge_triple (P : FAssn) : FTriple P diverge (fun _ _ => False) :=
  fun _ _ _ _ _ _ => trivial

/-- The model failure classes stay distinct constructors. -/
example : Error.unspecified ≠ Error.panic := by decide
example : Error.illegal ≠ Error.unspecified := by decide
example : Error.deadlock ≠ Error.panic := by decide
/-- An unsupported timer is not an unspecified result: reports can tell them apart. -/
example : Error.unsupportedTimer ≠ Error.unspecified := by decide
example : Error.trap ≠ Error.panic := by decide
example : Error.stackOverflow ≠ Error.panic := by decide

end OutcomeTaxonomy
