import ZigLean
import Air2Lean.StdModels
import Lean.Elab.Command

/-! E04: every semantic dependency of the built-in std model table names a declaration of the
`ZigLean` umbrella that generated source imports. Elaboration fails on a missing name. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let deps := Air2Lean.stdModels.flatMap (·.dependencies)
  let missing := deps.filter fun d => !env.contains d.toName
  unless missing.isEmpty do
    throwError m!"std model dependencies missing from ZigLean: {missing}"
  logInfo m!"std model dependencies resolved: {deps.size}"
