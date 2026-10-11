import Lean
import AuditClaims.Gen

/-!
Residual S1 counterexample after the claim-binding fix (S2-S6). `unchecked_total` fixes a root
argument, so the derived domain now scopes it; this variant quantifies every argument, has no
hypothesis and trivially inhabited premises, and would reach `functionally_verified_total`
without kernel replay (S1), which rejects this module. The S7 variant is in `AsmTotal.lean`, so
that each module's audit verdict belongs to one finding.
-/

open Lean Elab Command Term Meta

/-- S1: a kernel-unchecked universal claim (false: `root 255` panics). -/
elab "#audit_unchecked_universal" : command => do
  liftTermElabM do
    let type ← instantiateMVars (← elabType (← `(∀ x : BitVec 8, AuditClaims.root x = pure (x + 1))))
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.thmDecl { name := `AuditClaims.unchecked_universal, levelParams := [], type,
                          value := mkConst ``True.intro })

#audit_unchecked_universal

namespace AuditClaims

end AuditClaims
