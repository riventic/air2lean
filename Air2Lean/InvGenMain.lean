import Air2Lean.InvGen

/-!
The invariant generator as an executable (`lake build air2lean-invgen`):

    air2lean-invgen MODULE NAMESPACE [-o FILE]

It imports the translated `MODULE` (on the lookup path of `LEAN_PATH`, so run it under
`lake env`), reads its loops, and writes the generated invariants and measures
(`Air2Lean.InvGen.generate`) to `FILE` (default: stdout). Each loop it cannot handle is named on
stderr with the reason; it gets no definition. An error is printed on stderr, with exit code 1.
-/

open Lean Meta

unsafe def main (argv : List String) : IO UInt32 := do
  let (module, ns, out) := match argv with
    | [m, n] => (m, n, none)
    | [m, n, "-o", f] => (m, n, some f)
    | _ => ("", "", none)
  if module.isEmpty then
    IO.eprintln "usage: air2lean-invgen MODULE NAMESPACE [-o FILE]"
    return 2
  try
    initSearchPath (← findSysroot)
    -- The `match` and structure tables are environment extensions: load them as `lean` does.
    enableInitializersExecution
    let env ← importModules #[{ module := module.toName }] {} (loadExts := true)
    let ((text, skipped), _) ← (Air2Lean.InvGen.generate module.toName ns.toName).run'.toIO
      { fileName := "<air2lean-invgen>", fileMap := default, maxHeartbeats := 0 } { env }
    for (loop, why) in skipped do
      IO.eprintln s!"air2lean-invgen: {loop}: no invariant: {why}"
    match out with
    | some f => IO.FS.writeFile f text
    | none => IO.print text
    return 0
  catch error =>
    IO.eprintln s!"air2lean-invgen: {error}"
    return 1
