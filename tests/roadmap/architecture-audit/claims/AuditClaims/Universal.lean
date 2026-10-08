import Lean
import Proofs.Asm.Gen
import AuditClaims.Gen

/-!
Residual S1 and S7 counterexamples after the claim-binding fix (S2-S6). `unchecked_total` and
`asm_divmod_total` fix a root argument, so the derived domain now scopes them; these variants
quantify every argument, have no hypothesis and trivially inhabited premises, and therefore still
reach `functionally_verified_total` until kernel replay (S1) and `Result`-valued asm opaques (S7)
land.
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

/-- S7: the register-only asm opaque is total, so `divl` provably returns for every divisor,
including 0 (which traps natively). -/
theorem asm_divmod_universal (a b : BitVec 32) :
    Asm.divmod a b = pure (((Asm.airAsm_3653072158 a b).2.setWidth 64 <<< 32) |||
      (Asm.airAsm_3653072158 a b).1.setWidth 64) := by
  unfold Asm.divmod
  simp [zig_unfold, Zig.shl]

end AuditClaims
