import tools.Assurance

/-!
The assurance extractor as an executable (`lake build assurance`, scripts/assumptions.py):

    assurance --sysroot DIR [--all-declarations] [--family NAME]... MODULE...

It imports the selected modules once, with this extractor's own modules and without running an
interpreted initializer of any of them (`Air2Lean.Assurance.importAudited`), on the lookup path
of `LEAN_PATH` and then the library of the toolchain `DIR`, and prints one line
`AIR2LEAN_ASSURANCE_JSON:` and the report. A compiled extractor holds each module once: the
command it replaces ran in a `lean` process that had already imported the extractor's own closure
(the whole of `Lean`), which a second import copies. Resource limits are not audit checks: the
extractor runs without a heartbeat limit and with a raised `maxRecDepth` (fsym proofs set 20000),
so a failure stays one. An error is printed on stderr, with exit code 1.
-/

open Lean Meta

/-- The command line. -/
structure Args where
  sysroot : Option System.FilePath := none
  allDeclarations : Bool := false
  families : Array Name := #[]
  modules : Array String := #[]

def parseArgs (args : Args) : List String → Except String Args
  | [] => .ok args
  | "--sysroot" :: dir :: rest => parseArgs { args with sysroot := some dir } rest
  | "--all-declarations" :: rest => parseArgs { args with allDeclarations := true } rest
  | "--family" :: name :: rest => parseArgs { args with families := args.families.push name.toName } rest
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown or incomplete option {arg}"
    else parseArgs { args with modules := args.modules.push arg } rest

unsafe def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs {} argv with
    | .ok args => pure args
    | .error message => throw <| IO.userError s!"assurance: {message}"
  let some sysroot := args.sysroot | throw <| IO.userError "assurance: --sysroot DIR is required"
  try
    initSearchPath sysroot
    let modules := args.modules.map String.toName
    if let some m := args.modules.find? (·.toName.isAnonymous) then
      throw <| IO.userError s!"not a module name: {m}"
    let opts := maxRecDepth.set (maxHeartbeats.set {} 0) 100000
    let env ← Air2Lean.Assurance.importAudited modules opts
    let (result, _) ← (Air2Lean.Assurance.report args.modules args.allDeclarations args.families).toIO
      { fileName := "<assurance>", fileMap := default, options := opts, maxHeartbeats := 0,
        maxRecDepth := 100000 }
      { env }
    IO.println ("AIR2LEAN_ASSURANCE_JSON:" ++ result.compress)
    return 0
  catch error =>
    IO.eprintln s!"assurance: {error}"
    return 1
