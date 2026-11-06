import Lean
import AuditClaims.Gen

/-!
Residual S1 counterexample after the claim-binding fix (S2-S6). `unchecked_total` fixes a root
argument, so the derived domain now scopes it; this variant quantifies every argument, has no
hypothesis and trivially inhabited premises, and would reach `functionally_verified_total`
without kernel replay (S1), which rejects this module. The S7 variant is in `AsmTotal.lean`, so
that each module's audit verdict belongs to one finding.
-/

set_option debug.skipKernelTC true in
/-- S1: a kernel-unchecked universal claim (false: `root 255` panics), entered as in
`Unchecked.lean`. -/
theorem AuditClaims.unchecked_universal : ∀ x : BitVec 8, AuditClaims.root x = pure (x + 1) := by
  run_tac do (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkConst ``True.intro)
