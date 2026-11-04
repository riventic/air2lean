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

    assurance --sysroot DIR --closure MODULE...

prints the import closure of `tools.Assurance` and the modules, one name per line
(`Air2Lean.Assurance.importClosure`). The extractor runs itself this way first: the data that
reading the closure maps stays mapped until that process ends, so the audit's own import maps
every module once.
-/

open Lean Meta

/-- The command line. -/
structure Args where
  sysroot : Option System.FilePath := none
  allDeclarations : Bool := false
  closure : Bool := false
  families : Array Name := #[]
  modules : Array String := #[]

def parseArgs (args : Args) : List String → Except String Args
  | [] => .ok args
  | "--sysroot" :: dir :: rest => parseArgs { args with sysroot := some dir } rest
  | "--all-declarations" :: rest => parseArgs { args with allDeclarations := true } rest
  | "--closure" :: rest => parseArgs { args with closure := true } rest
  | "--family" :: name :: rest => parseArgs { args with families := args.families.push name.toName } rest
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown or incomplete option {arg}"
    else parseArgs { args with modules := args.modules.push arg } rest

/-- The import closure of `tools.Assurance` and `modules`, read by this program in a process of
its own (`--closure`). -/
def closureOf (sysroot : System.FilePath) (modules : Array String) : IO (Array Name) := do
  let out ← IO.Process.output
    { cmd := (← IO.appPath).toString, args := #["--sysroot", sysroot.toString, "--closure"] ++ modules }
  if out.exitCode != 0 then
    throw <| IO.userError s!"reading the import closure failed (exit code {out.exitCode}):\n{out.stderr}"
  return (out.stdout.splitOn "\n").filter (!·.isEmpty) |>.map String.toName |>.toArray

unsafe def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs {} argv with
    | .ok args => pure args
    | .error message => throw <| IO.userError s!"assurance: {message}"
  let some sysroot := args.sysroot | throw <| IO.userError "assurance: --sysroot DIR is required"
  try
    initSearchPath sysroot
    let modules := args.modules.map String.toName
    if args.closure then
      for m in ← Air2Lean.Assurance.importClosure (#[`tools.Assurance] ++ modules) do
        IO.println (m.toString (escape := false))  -- read back by `String.toName`
      return 0
    let opts := maxRecDepth.set (maxHeartbeats.set {} 0) 100000
    let env ← Air2Lean.Assurance.importAudited modules (← closureOf sysroot args.modules) opts
    let (result, _) ← (Air2Lean.Assurance.report args.modules args.allDeclarations args.families).toIO
      { fileName := "<assurance>", fileMap := default, options := opts, maxHeartbeats := 0,
        maxRecDepth := 100000 }
      { env }
    IO.println ("AIR2LEAN_ASSURANCE_JSON:" ++ result.compress)
    return 0
  catch error =>
    IO.eprintln s!"assurance: {error}"
    return 1
