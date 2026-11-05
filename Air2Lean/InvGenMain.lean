import Air2Lean.InvGen
import Air2Lean.Revision

/-!
The invariant generator as an executable (`lake build air2lean-invgen`):

    air2lean-invgen MODULE NAMESPACE --source FILE [-o FILE]

It imports the translated `MODULE` (on the lookup path of `LEAN_PATH`, so run it under
`lake env`), whose source is `--source FILE` (a path relative to the repository root), reads its
loops, and writes the generated invariants and measures (`Air2Lean.InvGen.generate`) to `-o FILE`
(default: stdout). The first line records the generator's revision (`translator_revision%`: this
file and the `Air2Lean` modules it imports) and the source's SHA-256, which
`scripts/gen-integrity.py invgen` checks against the checkout. Each loop it cannot handle is named
on stderr with the reason; it gets no definition. An error is printed on stderr, with exit code 1.
-/

open Lean Meta

/-- The generator's revision record. -/
def generatorRecord : Json :=
  let t := translator_revision%
  Json.mkObj [("lean", t.lean), ("revision", t.revision),
    ("modules", Json.arr (t.modules.map fun (m, h) => Json.arr #[m, h]))]

unsafe def main (argv : List String) : IO UInt32 := do
  let (module, ns, source, out) := match argv with
    | [m, n, "--source", s] => (m, n, s, none)
    | [m, n, "--source", s, "-o", f] => (m, n, s, some f)
    | _ => ("", "", "", none)
  if module.isEmpty then
    IO.eprintln "usage: air2lean-invgen MODULE NAMESPACE --source FILE [-o FILE]"
    return 2
  try
    let inputs := Json.arr #[Json.arr #[source,
      Air2Lean.Revision.sha256 (← IO.FS.readBinFile source)]]
    initSearchPath (← findSysroot)
    -- The `match` and structure tables are environment extensions. Loading them
    -- (`loadExts := true`) requires initializer execution, as in `lean` itself: the imported
    -- modules' initializers run here as they do when a proof imports the same module.
    enableInitializersExecution
    let env ← importModules #[{ module := module.toName }] {} (loadExts := true)
    -- The default heartbeat limit: a run is bounded and deterministic, never timed.
    let ((text, skipped), _) ←
      (Air2Lean.InvGen.generate module.toName ns.toName generatorRecord inputs).run'.toIO
        { fileName := "<air2lean-invgen>", fileMap := default } { env }
    for (loop, why) in skipped do
      IO.eprintln s!"air2lean-invgen: {loop}: no invariant: {why}"
    match out with
    | some f => IO.FS.writeFile f text
    | none => IO.print text
    return 0
  catch error =>
    IO.eprintln s!"air2lean-invgen: {error}"
    return 1
