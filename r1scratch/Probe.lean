import Nested.Gen
open Lean Meta
set_option pp.notation false
set_option pp.match false
set_option pp.fieldNotation false
set_option pp.structureInstances false
set_option pp.funBinderTypes true
set_option pp.instances false
#eval show MetaM Unit from do
  let some (.defnInfo d) := (← getEnv).find? `Nested.pairs.loop14 | throwError "no"
  logInfo m!"{d.value}"
  let some (.defnInfo m) := (← getEnv).find? `Nested.pairs.loop14.match_1 | throwError "nomatch"
  logInfo m!"{m.type}"
