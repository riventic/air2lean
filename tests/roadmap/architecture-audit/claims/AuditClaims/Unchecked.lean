import Lean
import AuditClaims.Gen

/-!
C9: a kernel-unchecked theorem. `debug.skipKernelTC` makes `addDecl` skip the kernel, and the
built-in `run_tac` closes the goal with an ill-typed proof (`True.intro` for a false equation), so
the theorem enters the environment and the `.olean`. `collectAxioms` finds no axiom and
`scripts/no-sorry.sh` greps only for sorry/admit/native_decide; only the kernel replay (S1:
`kernel-replay.sh` and `scripts/assumptions.py`) rejects this module.
The statement is false: `root 255` panics with `.overflow`.
-/

set_option debug.skipKernelTC true in
theorem AuditClaims.unchecked_total : AuditClaims.root 255 = pure 0 := by
  run_tac do (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkConst ``True.intro)
