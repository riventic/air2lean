import ZigLean.Sep.Full.Witness
import AuditClaims.Gen

/-!
Architecture-audit counterexamples (docs/architecture-audit/claims.md). Every theorem here is
kernel-checked with standard axioms only, mentions the generated root in its conclusion, and is
classified by `scripts/claims.py` at the strength noted. None of them is evidence that
`AuditClaims.root` is correct: `root 255` panics. The triples are full-state ones
(`FTriple`, `FTotalTriple`, `docs/sep-full-state.md`).
-/

open Zig Full FAssn Witness

namespace AuditClaims

/-- C1: the claim is a hypothesis. Hypotheses are stripped, so this is `total_correctness`. -/
theorem hyp_is_claim (x : BitVec 8) (h : root x = pure (x + 1)) : root x = pure (x + 1) := h

/-- C2: unsatisfiable precondition (`x.toNat > 300` for an 8-bit `x`). `total_correctness`. -/
theorem unsat_pre (x : BitVec 8) (hx : x.toNat > 300) : root x = pure (x + 1) := by
  have := x.isLt; omega

/-- C3: one ground input. `total_correctness`; the manifest `domain` string is not checked. -/
theorem ground_instance : root 3 = pure 4 := rfl

/-- C4: `FTotalTriple` with precondition `False`. `total_correctness`. -/
theorem total_false_pre (Q : Unit → FAssn) : FTotalTriple (fun _ => False) spin Q :=
  ⟨fun _ _ _ _ hp _ => hp.elim, fun _ _ _ _ hp _ => hp.elim⟩

/-- C5: the root occurs only inside the postcondition of a triple about `pure ()`.
`conclusion_dependencies` contains `AuditClaims.root`, so coverage binds this as `direct`. -/
theorem root_in_post :
    FTotalTriple emp (pure () : MemM Unit) (fun _ => ⟪root 255 = root 255⟫) :=
  (FTotalTriple.ret (Q := fun _ => ⟪root 255 = root 255⟫) ()).pre fun _ h => ⟨rfl, h⟩

/-- C6: an exact-success equation whose left side is not the root at all; the root is only an
ignored argument on the right. `total_correctness`, `direct`. -/
theorem root_ignored : (pure 5 : Result Nat) = pure (Function.const _ 5 (root 255)) := rfl

/-- C7: partial correctness of a program that never returns, with postcondition `False`.
`partial_correctness`: coverage reported `functionally_verified_partial`. Its precondition is
satisfiable (witness below), so only the missing liveness witness (S6) caps it. -/
theorem spin_partial : FTriple emp spin (fun _ _ => False) :=
  fun _ _ _ _ _ _ => trivial

nonvacuity_witness spin_partial := FAdmit.of_mem ⟨by funext l; rfl, rfl, rfl⟩ fseq_default

end AuditClaims
