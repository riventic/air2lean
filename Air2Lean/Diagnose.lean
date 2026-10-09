import Air2Lean.Check
import Air2Lean.Air.Normalize
import Air2Lean.Air.Anon

/-! Check-only diagnostic collection. No emitter, compiler or proof checker runs here. -/
namespace Air2Lean.Diagnostics
open Lean

def maxFiles : Nat := 256
def maxInputBytes : Nat := 64 * 1024 * 1024

structure CheckArgs where
  directory : System.FilePath
  profile : Option String := none
  limit : Nat := 256
  spawnPolicy : SpawnSemantics := .available
  allowUnqualified : Bool := false

private partial def parseOptions (args : List String) (out : CheckArgs)
    (spawnPolicySeen : Bool := false) : Except String CheckArgs := do
  match args with
  | [] => return out
  | "--profile" :: p :: rest =>
    unless p == BuildProfile.legacyName || p == BuildProfile.currentName do throw "invalid --profile"
    if out.profile.isSome then throw "duplicate --profile"
    parseOptions rest { out with profile := some p } spawnPolicySeen
  | "--allow-unqualified-build-mode" :: rest =>
    parseOptions rest { out with allowUnqualified := true } spawnPolicySeen
  | "--diagnostic-limit" :: value :: rest =>
    let some limit := value.toNat? | throw "--diagnostic-limit must be an integer"
    unless 1 ≤ limit && limit ≤ 4096 do throw "--diagnostic-limit must be from 1 through 4096"
    parseOptions rest { out with limit } spawnPolicySeen
  | "--spawn-policy" :: value :: rest =>
    if spawnPolicySeen then throw "duplicate --spawn-policy"
    let spawnPolicy ← parseSpawnPolicy value
    parseOptions rest { out with spawnPolicy } true
  | ["--spawn-policy"] => throw "missing value for --spawn-policy"
  | _ => throw "check-only mode accepts only <air-dir>, --profile, --allow-unqualified-build-mode, --diagnostic-limit and --spawn-policy; emission flags are incompatible"

def parseCheckArgs (args : List String) : Except String CheckArgs := do
  match args with
  | "--diagnostics-json" :: directory :: options =>
    if directory.startsWith "-" then throw "missing <air-dir>"
    if directory.length > 1024 then throw "AIR directory path exceeds 1024 characters"
    parseOptions options { directory := directory }
  | _ => throw "usage: air2lean --diagnostics-json <air-dir> [--profile <name>] [--allow-unqualified-build-mode] [--diagnostic-limit 1..4096] [--spawn-policy available|fallible]"

structure FileResult where
  file : String
  function : Option String := none
  decodedProfile : Option BuildProfile := none
  normalized : Option Func := none
  index : Option OperandTypes := none
  structureValid : Bool := false
  localPassed : Bool := false
  /-- Individually normalized direct calls of a canonical function that is blocked before
  full normalization. They contribute dependency edges only; no partial function is built. -/
  blockedCalls : Array Inst := #[]

def FileResult.toJson (u : FileResult) : Json := Json.mkObj [
  ("file", Lean.toJson u.file), ("function", Lean.toJson u.function),
  ("normalized", Lean.toJson u.normalized.isSome), ("structure_valid", Lean.toJson u.structureValid),
  ("local_check", Lean.toJson (if u.localPassed then "passed" else "blocked_or_rejected"))]

private def FileResult.operandIndex (u : FileResult) (f : Func) : OperandTypes :=
  match u.index with
  | some index => index
  | none => f.operandTypes

structure Edge where
  caller : String
  callee : String
  instruction : Nat
  file : String

/-- Only named direct calls and explicit comptime spawn workers are observed.
Recognized runtime models do not need an AIR definition. -/
def edges (units : Array FileResult) : Array Edge := Id.run do
  let mut result := #[]
  for u in units do
    let source := if u.structureValid then
        u.normalized.map fun f => (f.name, (u.operandIndex f).insts)
      else u.function.map (·, u.blockedCalls)
    if let some (caller, insts) := source then
      for i in insts do
        if let .call (.func callee false worker) _ := i.op then
          if !modelledStdFn callee then
            result := result.push { caller, callee, instruction := i.id, file := u.file }
          if ((threadFn? callee).bind (·.spawnArgs?)).isSome then
            if let some callee := worker then
              result := result.push { caller, callee, instruction := i.id, file := u.file }
  return result

private def adjacency (graph : Array Edge) : Std.HashMap String (Array String) := Id.run do
  let mut reversed : Std.HashMap String (List String) := {}
  let mut seen : Std.HashMap String (Std.HashSet String) := {}
  for edge in graph do
    let neighbors := seen.getD edge.caller {}
    if neighbors.contains edge.callee then continue
    seen := seen.insert edge.caller (neighbors.insert edge.callee)
    reversed := reversed.insert edge.caller (edge.callee :: reversed.getD edge.caller [])
  return reversed.fold (init := ({} : Std.HashMap String (Array String))) fun index caller callees =>
    index.insert caller callees.reverse.toArray

private def pathsFrom (index : Std.HashMap String (Array String)) (start : String)
    (maxNodes : Nat) (goal : Option String := none) : Std.HashMap String (Array String) := Id.run do
  let mut queue : Array String := #[start]
  let mut paths : Std.HashMap String (Array String) := ({} : Std.HashMap String (Array String)).insert start #[start]
  let mut cursor := 0
  while h : cursor < queue.size do
    let current := queue[cursor]
    cursor := cursor + 1
    let some path := paths[current]? | return paths
    for callee in index[current]?.getD #[] do
      -- Terminal names cannot lead to another caller. Keep an explicitly requested
      -- terminal goal, but do not let missing leaf symbols exhaust coverage BFS.
      if (index.contains callee || goal == some callee) && !paths.contains callee then
        if queue.size ≥ maxNodes then return paths
        paths := paths.insert callee (path.push callee)
        queue := queue.push callee
  return paths

/-- Deterministic shortest named-call path; cycles and terminal symbols are bounded.
Absence is unavailable evidence, not a claim that no dependency exists. -/
def shortestChain (graph : Array Edge) (start goal : String) (maxNodes : Nat := maxFiles + 1) : Option (Array String) :=
  (pathsFrom (adjacency graph) start maxNodes (some goal))[goal]?

private def boundary (file : String) (function : Option String) (code : Code)
    (phase : Phase) (category : Category) (message : String := "") : Diagnostic :=
  { file := some file, function, code, phase, category, message }

/-- Explicit exporter and fast-math markers, reported with exported IDs before canonicalization. -/
private def marked (i : Raw.RawInst) : Bool :=
  i.tag.endsWith "_optimized" || i.unsupported

/-- One instruction without its nested bodies; those are flattened and inspected separately. -/
private def shallow (i : Raw.RawInst) : Raw.RawInst :=
  { i with body := #[], thenBody := #[], elseBody := #[],
           cases := i.cases.map fun c => { c with body := #[] } }

/-- After the composed normalizer failed, normalize each canonical instruction on its own so
one rejected tag cannot hide independent siblings. Only the version gate is unit-wide. Marked
instructions were already reported. Successfully normalized direct calls are retained for
dependency edges; no partial function, SSA value or replacement instruction is built. -/
def collectNormalization (file : String) (canonical : Raw.RawFunc) (hasMarkers : Bool)
    (whole : Except String Func) (initial : Log) : Array Inst × Log := Id.run do
  let name := some canonical.name
  let context := boundary file name .normalizationFailure .normalize .validationFailure
  if !supportedVersions.contains canonical.zigVersion then
    return (#[], initial.record context whole)
  let mut log := initial
  let mut calls : Array Inst := #[]
  let mut found := false
  for raw in Raw.flatten canonical.body do
    if marked raw then continue
    match normalizeInst canonical.name (shallow raw) with
    | .ok i => if let .call (.func ..) _ := i.op then calls := calls.push i
    | .error message =>
      found := true
      log := log.add { context with
        message
        category := if (runtimeTagReason? raw.tag).isSome then .unsupportedSemantics else .validationFailure
        anchor := { idSpace := .canonical, instruction := some raw.id }
        firstErrorInUnit := true }
  -- Defensive: never let an unexplained composed failure pass silently.
  if !found && !hasMarkers then log := log.record context whole
  return (calls, log)

/-- Pure per-file boundary used by both the CLI and kernel-checked regressions. -/
def inspect (file contents : String) (initial : Log) : FileResult × Log := Id.run do
  let mut log := initial
  let empty : FileResult := { file }
  let parsed := StrictJson.parse contents
  let .ok json := parsed
    | log := log.record (boundary file none .jsonSyntax .decode .malformedInput) parsed
      return (empty, log.add (skipped file none .normalize "decoded_AIR"))
  let name := (json.getObjValAs? String "name").toOption
  if (name.map (fun n => decide (n.length > 1024))).getD false then
    log := log.add (boundary file none .inputLimit .decode .resourceLimit "function name exceeds 1024 characters")
    return (empty, log.add (skipped file none .normalize "bounded_function_identity"))
  let unit := { empty with function := name }
  let decoded := Raw.parseFunc json
  let .ok raw := decoded
    | log := log.record (boundary file name .airDecode .decode .validationFailure) decoded
      return (unit, log.add (skipped file name .normalize "decoded_AIR"))
  let unit := { unit with function := some raw.name, decodedProfile := some raw.profile }
  let mut hasMarkers := false
  for i in Raw.flatten raw.body do
    if marked i then
      hasMarkers := true
      let message := match runtimeTagReason? i.tag with
        | some reason => s!"{raw.name}: inst {i.id}: tag '{i.tag}': {reason}"
        | none => s!"instruction tag '{i.tag}' is explicitly unsupported{markedTagGuidance i.tag}"
      log := log.add { (boundary file name
        (if i.tag.endsWith "_optimized" then .optimizedUnsupported else .exporterUnsupported)
        .normalize .unsupportedSemantics message) with
        anchor := { idSpace := .exported, instruction := some i.id } }
  -- Markers do not stop canonicalization (its rewrites match specific supported tags); a
  -- canonical failure stays its own fatal error. Unmarked siblings are normalized below.
  let rewritten := Raw.canonicalize raw
  let .ok canonical := rewritten
    | log := log.record (boundary file name .canonicalFailure .canonicalize .validationFailure) rewritten
      return (unit, log.add (skipped file name .check "canonicalized_AIR"))
  let normalized := normalizeCanonical canonical
  let .ok f := normalized
    | let (blockedCalls, collected) := collectNormalization file canonical hasMarkers normalized log
      return ({ unit with blockedCalls }, collected.add (skipped file name .check "fully_normalized_function"))
  let before := log.observed
  let checked := collectFunctionChecksDetailed file f log
  log := checked.log
  -- A final compatibility check catches any checks not decomposed above. It is
  -- skipped only when rejection is already established, never when accepting.
  if log.observed == before then
    log := log.record (boundary file name .instructionFailure .check .validationFailure) (check f)
  return ({ unit with
    normalized := some f
    index := some checked.index
    structureValid := checked.structureValid
    localPassed := checked.structureValid && log.observed == before }, log)

def collectProgram (units : Array FileResult) (initial : Log)
    (spawnPolicy : SpawnSemantics := .available) : Log := Id.run do
  let mut log := initial
  let safe := units.filter (·.structureValid)
  let funcs := safe.filterMap (·.normalized)
  let snapshot := CallChecksSnapshot.build funcs
  let mut selected : Std.HashMap String (Array FileResult) := {}
  for u in units do
    if let some name := u.function then
      selected := selected.insert name ((selected[name]?.getD #[]).push u)
  let mut names : Std.HashSet String := {}
  for u in units do
    if let some name := u.function then
      if !names.contains name then
        names := names.insert name
        if (selected[name]?.getD #[]).size > 1 then
          log := log.add (boundary u.file (some name) .duplicateFunction .program .malformedInput "function identity occurs in multiple selected files")
  for u in safe do
    if let some f := u.normalized then
      log := collectCallChecksIndexed u.file f (u.operandIndex f) snapshot log
  if !log.truncated then
    let graph := edges units
    let mut blockers : Array (Edge × Code × Option String) := #[]
    for edge in graph do
      let targets := selected[edge.callee]?.getD #[]
      let unsupported := if targets.isEmpty then rejectedThreadFn? edge.callee else none
      let code := if unsupported.isSome then some Code.modelFailure
        else if targets.isEmpty then some Code.calleeMissing
        else if targets.size > 1 then some Code.calleeAmbiguous
        else if !(targets[0]?.map (·.localPassed)).getD false then some Code.calleeBlocked else none
      if let some code := code then
        blockers := blockers.push (edge, code, unsupported)
    if !blockers.isEmpty then
      let index := adjacency graph
      for root in units do
        if log.truncated then break
        if let some name := root.function then
          let paths := pathsFrom index name (maxFiles + 1)
          for (edge, code, unsupported) in blockers do
            if log.truncated then break
            if let some chain := paths[edge.caller]? then
              log := log.add { (boundary edge.file (some edge.caller) code .program
                (if unsupported.isSome then .unsupportedSemantics else .validationFailure)
                (unsupported.getD "named dependency is absent, ambiguous or blocked; see diagnostic code")) with
                anchor := { idSpace := .canonical, instruction := some edge.instruction }
                dependencyChain := chain.push edge.callee }
  -- Retain the authoritative whole-program validator. Its first-error boundary
  -- includes shared definitions and memory effects not independently collected.
  if !funcs.isEmpty then
    let program := checkProgram funcs
    log := log.record {
      code := .programFailure
      phase := .program
      category := .validationFailure
      message := ""
      prerequisites := #["structurally_valid_selected_functions"] } program
    if spawnPolicy == .fallible then
      if program.toOption.isSome then
        log := log.record {
          code := .modelFailure
          phase := .program
          category := .unsupportedSemantics
          message := ""
          prerequisites := #["validated_selected_program"] } (checkFallibleSpawnCalls funcs)
      else
        log := log.add {
          code := .prerequisiteSkipped
          phase := .program
          category := .skipped
          message := "not inspected: fallible spawn policy requires a valid selected program"
          prerequisites := #["validated_selected_program"]
          firstErrorInUnit := true }
  if units.any (!·.localPassed) then
    log := { log with complete := false }
  return log

def report (units : Array FileResult) (log : Log) : Json := Json.mkObj [
  ("schema", Lean.toJson (1 : Nat)), ("kind", Lean.toJson "air2lean-check-diagnostics"),
  ("status", Lean.toJson (if log.failed then "rejected" else "checked")),
  ("complete", Lean.toJson log.complete), ("truncated", Lean.toJson log.truncated),
  ("diagnostic_limit", Lean.toJson log.limit), ("diagnostics_observed", Lean.toJson log.observed),
  ("diagnostic_payload_bytes", Lean.toJson log.payloadBytes),
  ("diagnostics", Json.arr (log.items.map Diagnostic.toJson)),
  ("files", Json.arr (units.map FileResult.toJson)),
  ("scope", Lean.toJson "selected AIR validation; first error within opaque prerequisite units"),
  ("proof_status", Lean.toJson "not_run"), ("runtime_outcomes", Lean.toJson "not_observed"),
  ("dependency_completeness", Lean.toJson "not_attested; direct normalized calls and explicit spawn workers only"),
  ("source_correspondence", Lean.toJson "not_attested")]

/-- Charge every returned chunk before decoding or a later I/O failure. The shared counter
survives rejected files. Readers follow `Handle.read`'s requested-size contract; across
serial calls only one byte beyond the aggregate budget is read to detect growth. -/
def readCharged (read : USize → IO ByteArray) (charged : IO.Ref Nat)
    (budget : Nat := maxInputBytes) : IO String := do
  let total ← charged.get
  if total > budget then
    throw (IO.userError "AIR input exceeds remaining aggregate budget")
  let bytes ← StrictJson.readBounded (fun request => do
    let chunk ← read request
    charged.modify (· + chunk.size)
    return chunk) (budget - total)
  let some contents := String.fromUTF8? bytes | throw (IO.userError "non UTF-8 AIR input")
  return contents

private inductive InputFailure where
  | limit
  | read (message : String)

private def readInput (path : System.FilePath) (charged : IO.Ref Nat) : IO (Except InputFailure String) := do
  try
    -- One fresh pre-open metadata snapshot; preserve size-before-kind classification.
    let metadata ← path.metadata
    let total ← charged.get
    if total > maxInputBytes || metadata.byteSize.toNat > maxInputBytes - total then
      return .error .limit
    unless metadata.type == .file do throw (IO.userError "AIR input must be a regular file")
    let contents ← IO.FS.withFile path .read fun handle => readCharged handle.read charged
    return .ok contents
  catch error => return .error (.read error.toString)

private def scan (a : CheckArgs) : IO (Array FileResult × Log) := do
  let mut log : Log := { limit := a.limit }
  let entries ← a.directory.readDir
  let paths := ((entries.filter fun e => e.fileName.endsWith ".json").qsort
    (fun x y => decide (x.fileName < y.fileName))).map (·.path)
  if paths.isEmpty then
    return (#[], log.add (boundary a.directory.toString none .inputRead .input .ioFailure "no *.json files found"))
  if paths.size > maxFiles then
    log := log.add { (boundary a.directory.toString none .inputLimit .input .resourceLimit
      s!"selected input exceeds {maxFiles} files; only the first sorted files are inspected") with
      firstErrorInUnit := true }
  let charged ← IO.mkRef (0 : Nat)
  let mut files : Array String := #[]
  let mut texts : Array String := #[]
  let mut units : Array FileResult := #[]
  for path in paths.extract 0 maxFiles do
    match ← readInput path charged with
    | .error .limit =>
      log := log.add { (boundary path.toString none .inputLimit .input .resourceLimit
        "AIR input exceeds remaining aggregate 64 MiB budget") with
        firstErrorInUnit := true }
      units := units.push { file := path.toString }
      log := log.add (skipped path.toString none .decode "readable_input_within_aggregate_budget")
    | .error (.read message) =>
      log := log.add { (boundary path.toString none .inputRead .input .ioFailure message) with firstErrorInUnit := true }
      units := units.push { file := path.toString }
      log := log.add (skipped path.toString none .decode "readable_UTF8_input")
    | .ok contents =>
      files := files.push path.toString
      texts := texts.push contents
  let renamed := Anon.renumberAll texts
  let mut firstProfile : Option BuildProfile := none
  for (file, contents) in files.zip renamed do
    let result := inspect file contents log
    log := result.2
    if let some profile := result.1.decodedProfile then
      let baseline := firstProfile.getD profile
      firstProfile := some baseline
      log := log.record (boundary file result.1.function .profileFailure .profile .validationFailure)
        (BuildProfile.checkProgram #[baseline, profile] a.profile a.allowUnqualified)
    units := units.push { result.1 with decodedProfile := none }
  units := units.qsort (fun x y => decide (x.file < y.file))
  return (units, collectProgram units log a.spawnPolicy)

def runCheck (args : List String) : IO UInt32 := do
  let result ← match parseCheckArgs args with
    | .error message => pure (#[], ({ } : Log).add {
        code := .cliArguments
        phase := .cli
        category := .malformedInput
        message
        firstErrorInUnit := true })
    | .ok a =>
      try scan a catch error =>
        pure (#[], ({ limit := a.limit } : Log).add {
          code := .inputRead
          phase := .input
          category := .ioFailure
          message := error.toString
          firstErrorInUnit := true })
  IO.println (report result.1 result.2).compress
  return if result.2.failed then 1 else 0

end Air2Lean.Diagnostics
