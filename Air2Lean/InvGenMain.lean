import Air2Lean.InvGen
import Air2Lean.Revision

/-!
The invariant generator as an executable (`lake build air2lean-invgen`):

    air2lean-invgen MODULE NAMESPACE --source FILE [--spec MODULE FILE]... [--contract NAME]...
      --fingerprints FILE [-o FILE]

`--fingerprints FILE` (a JSON list of `[definition, fingerprint]`, `scripts/invgen.py`) gives the
semantic fingerprints of the translated functions; the record names, per loop, the function that
runs it and its fingerprint.

It imports the translated `MODULE`, whose source is `--source FILE` (a path relative to the
repository root), and the library `ZigLean.Sep.Full.AutoAll`, whose `fsym` prunes the candidate
invariants, with `ZigLean.Sep.Full.Cost`, whose counted loop rule states the step of the credit
mode (all on the lookup path of `LEAN_PATH`: run it under `lake env` after
`lake build ZigLean.Sep.Full.AutoAll ZigLean.Sep.Full.Cost`). `--spec MODULE FILE` imports a hand-written specification
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

/-- The options after `MODULE NAMESPACE --source FILE`. -/
structure CliOptions where
  /-- The specification modules with their sources (`--spec MODULE FILE`). -/
  specs : Array (String × String) := #[]
  /-- The contracts (`--contract NAME`). -/
  contracts : Array String := #[]
  /-- The semantic fingerprints of the translated functions (`--fingerprints FILE`, required). -/
  fingerprints : Option String := none
  /-- The output (`-o FILE`). -/
  out : Option String := none

/-- The options after `MODULE NAMESPACE --source FILE`; `none`: not an option list. -/
def options : List String → Option CliOptions
  | [] => some {}
  | "--spec" :: m :: f :: rest => (options rest).map fun o => { o with specs := #[(m, f)] ++ o.specs }
  | "--contract" :: c :: rest => (options rest).map fun o => { o with contracts := #[c] ++ o.contracts }
  | "--fingerprints" :: f :: rest => (options rest).map fun o => { o with fingerprints := some f }
  | ["-o", f] => some { out := some f }
  | _ => none

unsafe def main (argv : List String) : IO UInt32 := do
  let usage : IO UInt32 := do
    IO.eprintln "usage: air2lean-invgen MODULE NAMESPACE --source FILE \
      [--spec MODULE FILE]... [--contract NAME]... --fingerprints FILE [-o FILE]"
    return 2
  let module :: ns :: "--source" :: source :: rest := argv | usage
  let some { specs, contracts, fingerprints := some fps, out } := options rest | usage
  try
    -- `[[definition, fingerprint], …]` of the translated functions
    let fingerprints ← IO.ofExcept <|
      (Json.parse (← IO.FS.readFile fps)).bind (fromJson? (α := Array (String × String)))
    let mut inputs : Array Json := #[]
    let files : Array String := #[source] ++ specs.map fun (spec : String × String) => spec.2
    for file in files do
      inputs := inputs.push
        (Json.arr #[Json.str file, Json.str (Air2Lean.Revision.sha256 (← IO.FS.readBinFile file))])
    initSearchPath (← findSysroot)
    -- The `match` and structure tables are environment extensions. Loading them
    -- (`loadExts := true`) requires initializer execution, as in `lean` itself: the imported
    -- modules' initializers run here as they do when a proof imports the same module.
    enableInitializersExecution
    -- With the library and `fsym`, for the pruning walks (`Air2Lean.InvGen.houdini`), and the
    -- counted loop rule's step (`ZigLean.Sep.Full.Cost`), for the check of the credit mode.
    let specNames : Array Name := specs.map fun (spec : String × String) => spec.1.toName
    let imports : Array Import :=
      #[{ module := module.toName }, { module := `ZigLean.Sep.Full.AutoAll },
        { module := `ZigLean.Sep.Full.Cost }] ++
        specNames.map fun (m : Name) => ({ module := m } : Import)
    let env ← importModules imports {} (loadExts := true)
    -- The default heartbeat limit: a run is bounded and deterministic, never timed.
    let ((text, skipped), _) ←
      (Air2Lean.InvGen.generate module.toName ns.toName generatorRecord (Json.arr inputs)
        specNames (contracts.map fun (c : String) => c.toName) fingerprints).run'.toIO
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
