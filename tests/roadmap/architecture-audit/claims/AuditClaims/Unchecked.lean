import Lean
import AuditClaims.Gen

/-!
C9: a kernel-unchecked theorem. `debug.skipKernelTC` makes `addDecl` skip the kernel, so an
ill-typed proof (`True.intro` for a false equation) enters the environment and the `.olean`.
`collectAxioms` finds no axiom, `scripts/no-sorry.sh` greps only for sorry/admit/native_decide,
and nothing in the gate replays the environment through the kernel.
The statement is false: `root 255` panics with `.overflow`.
-/

open Lean Elab Command Term Meta

elab "#audit_unchecked_theorem" : command => do
  liftTermElabM do
    let type ← instantiateMVars (← elabType (← `(AuditClaims.root 255 = pure 0)))
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.thmDecl { name := `AuditClaims.unchecked_total, levelParams := [], type,
                          value := mkConst ``True.intro })

#audit_unchecked_theorem
