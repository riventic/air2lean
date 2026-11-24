import Air2Lean.InvGen
import Air2Lean.Revision

/-!
The invariant generator as an executable (`lake build air2lean-invgen`):

    air2lean-invgen MODULE NAMESPACE --source FILE [--spec MODULE FILE]... [--contract NAME]... [-o FILE]

It imports the translated `MODULE`, whose source is `--source FILE` (a path relative to the
repository root), and the library `ZigLean.Sep.Full.AutoAll`, whose `fsym` prunes the candidate
invariants (both on the lookup path of `LEAN_PATH`: run it under `lake env` after
`lake build ZigLean.Sep.Full.AutoAll`). `--spec MODULE FILE` imports a hand-written specification
module too (its source `FILE` is recorded as an input), and `--contract NAME` names a theorem of
it: the contract of a function that a loop calls. With contracts, the output holds the loops that
call by one of them (the others are in the module's file generated without contracts). It reads the module's loops, and writes the generated
invariants and measures (`Air2Lean.InvGen.generate`) to `-o FILE` (default: stdout). The first line records the generator's revision (`translator_revision%`: this
file and the `Air2Lean` modules it imports) and the source's SHA-256, which
`scripts/gen-integrity.py invgen` checks against the checkout: the caller builds `MODULE`'s olean
from that source (`scripts/invgen.py` compiles it fresh), since only the source is hashed. Each loop it cannot handle is named
on stderr with the reason; it gets no definition. An error is printed on stderr, with exit code 1.
-/

open Lean Meta

/-- The generator's revision record. -/
def generatorRecord : Json := toJson translator_revision%

/-- The options after `MODULE NAMESPACE --source FILE`: the specification modules with their
sources (`--spec MODULE FILE`), the contracts (`--contract NAME`) and the output (`-o FILE`);
`none`: not an option list. -/
def options : List String → Option (Array (String × String) × Array String × Option String)
  | [] => some (#[], #[], none)
  | "--spec" :: m :: f :: rest => (options rest).map fun (ss, cs, o) => (#[(m, f)] ++ ss, cs, o)
  | "--contract" :: c :: rest => (options rest).map fun (ss, cs, o) => (ss, #[c] ++ cs, o)
  | ["-o", f] => some (#[], #[], some f)
  | _ => none

unsafe def main (argv : List String) : IO UInt32 := do
  let parsed := match argv with
    | m :: n :: "--source" :: s :: rest => (options rest).map fun (ss, cs, o) => (m, n, s, ss, cs, o)
    | _ => none
  let some (module, ns, source, specs, contracts, out) := parsed
    | IO.eprintln "usage: air2lean-invgen MODULE NAMESPACE --source FILE \
        [--spec MODULE FILE]... [--contract NAME]... [-o FILE]"
      return 2
  try
    let mut inputs := #[]
    for file in #[source] ++ specs.map (·.2) do
      inputs := inputs.push (Json.arr #[file, Air2Lean.Revision.sha256 (← IO.FS.readBinFile file)])
    initSearchPath (← findSysroot)
    -- The `match` and structure tables are environment extensions. Loading them
    -- (`loadExts := true`) requires initializer execution, as in `lean` itself: the imported
    -- modules' initializers run here as they do when a proof imports the same module.
    enableInitializersExecution
    -- With the library and `fsym`, for the pruning walks (`Air2Lean.InvGen.houdini`).
    let env ← importModules (#[{ module := module.toName }, { module := `ZigLean.Sep.Full.AutoAll }] ++
      specs.map fun (m, _) => { module := m.toName }) {} (loadExts := true)
    -- The default heartbeat limit: a run is bounded and deterministic, never timed.
    let ((text, skipped), _) ←
      (Air2Lean.InvGen.generate module.toName ns.toName generatorRecord (Json.arr inputs)
        (specs.map (·.1.toName)) (contracts.map (·.toName))).run'.toIO
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
