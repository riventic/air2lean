import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
import Air2Lean.Air.Anon
import Air2Lean.Diagnose
import Air2Lean.SourceMap
import Air2Lean.ModuleSplit
import Air2Lean.Revision
import Air2Lean.Device
import Air2Lean.Certificate
import Air2Lean.OpTable

/-!
# CLI

`air2lean <air-dir> -o <out.lean> --namespace <Ns> [--prefix <p>]` reads every `*.json` file in
`<air-dir>` (`docs/air-json.md`), parses + normalizes + checks each into a `Func`
(`Air2Lean/Air/{Json,Normalize}.lean`, `Air2Lean/Check.lean`), then emits them all as one Lean
file (`Air2Lean/Emit.lean`) importing `ZigLean`, under `namespace <Ns>`. Before parsing, each
`__anon_<n>` of a generic instance gets a stable number (`Air2Lean/Air/Anon.lean`).

Exits 1 with a message on any error at any stage: a bad flag, an unparsable/unsupported AIR
file, or a function outside the checked subset.

`--timing-json <path>` additionally writes per-phase monotonic wall times after a successful
run (`docs/perf-budgets.md`). It only observes the stages; the Lean output is unchanged.
`--source-map-json <path>` likewise writes a per-function source map and canonical bodies
for semantic fingerprints (`docs/stable-generation.md`, `Air2Lean/SourceMap.lean`).
`--split-modules <Root>` writes the same declarations as one module per call group under
`<out>/` plus an umbrella `-o` module (`docs/modular-output.md`, `Air2Lean/ModuleSplit.lean`).
`--air-certificate <path> --air-certificate-import <Module>` likewise writes a Lean file of
AIR semantics certificates against the generated module `<Module>`
(`docs/air-semantics.md`, `Air2Lean/Certificate.lean`).
-/

namespace Air2Lean

/-- The sources this CLI was built from (`Air2Lean/Revision.lean`). -/
def translator : Revision.Translator := translator_revision%

/-- `translator` as recorded in the source-map sidecar and the module manifest. -/
def translatorJson : Lean.Json := Lean.Json.mkObj [("lean", .str translator.lean),
  ("revision", .str translator.revision),
  ("modules", .arr (translator.modules.map fun (m, h) => .arr #[.str m, .str h]))]

def usage : String :=
  "usage: air2lean <air-dir> -o <out.lean> --namespace <Ns> [--prefix <p>] " ++
    "[--float-semantics ieee|compiler-rt] [--spawn-policy available|fallible] [--profile legacy-abi64-le|abi64-le-v1|abi64-be-v1] [--allow-unqualified-build-mode] [--model-registry <json>] [--model-registry-template] [--proof-api] [--timing-json <json>] [--source-map-json <json>] [--split-modules <Module>] [--device-contract <json>] [--air-certificate <lean> --air-certificate-import <Module>] [--allocator-model std|translated]\n" ++
    "       air2lean --diagnostics-json <air-dir> [--profile <name>] [--allow-unqualified-build-mode] [--diagnostic-limit 1..4096] [--unit-diagnostic-limit 1..4096] [--spawn-policy available|fallible] [--device-contract <json>] [--allocator-model std|translated]\n" ++
    "       air2lean --print-op-table"

def help : String :=
  "Translate exported Zig AIR JSON into Lean definitions.\n\n" ++ usage ++
  "\n\nArguments:\n" ++
  "  <air-dir>                    Directory of JSON files from the patched Zig compiler.\n" ++
  "  -o <out.lean>                Lean file to write (required).\n" ++
  "  --namespace <Ns>             Lean namespace, such as My.Program (required).\n" ++
  "  --prefix <p>                 Trim this prefix from emitted function names.\n" ++
  "  --float-semantics <mode>      ieee (default) or compiler-rt; see docs/floats.md.\n" ++
  "  --spawn-policy <policy>      available (default) or fallible; see docs/spawn-failure.md.\n" ++
  "  --profile <name>             Require this input build profile; see docs/profiles.md.\n" ++
  "                               AIR schemas 1-11 need --profile legacy-abi64-le.\n" ++
  "  --allow-unqualified-build-mode  Also translate AIR of a build mode/backend that\n" ++
  "                               docs/build-modes.md does not qualify (recorded in the header).\n" ++
  "  --model-registry <json>      Bind external calls to user models; see docs/external-models.md.\n" ++
  "  --model-registry-template    Write a registry template to -o instead of Lean.\n" ++
  "  --proof-api                  Emit stable model/unfold/loop-step lemmas; see docs/generated-code.md.\n" ++
  "  --device-contract <json>     Model volatile integer accesses as device events; see docs/volatile-effects.md.\n" ++
  "  --allocator-model <mode>     std (default) or translated; see docs/allocator-model.md.\n" ++
  "  --diagnostics-json           Check only and print JSON diagnostics; see docs/diagnostics.md.\n" ++
  "  --diagnostic-limit <n>       Diagnostics to report in that mode (1..4096).\n" ++
  "  --unit-diagnostic-limit <n>  Diagnostics to report per input file in that mode (1..4096).\n" ++
  "  --timing-json <json>         Also write per-phase wall times; see docs/perf-budgets.md.\n" ++
  "  --source-map-json <json>     Also write source maps for fingerprints; see docs/stable-generation.md.\n" ++
  "  --split-modules <Module>     Write one module per call group; -o is the umbrella <Module>.\n" ++
  "                               See docs/modular-output.md.\n" ++
  "  --air-certificate <lean>     Also write AIR semantics certificates; see docs/air-semantics.md.\n" ++
  "  --air-certificate-import <M> The module the certificates import (the generated -o file).\n" ++
  "  --print-op-table             Print every known AIR tag's op, effect class and emitter route (JSON).\n" ++
  "  -h, --help                   Show this help.\n\n" ++
  "Supported AIR: Zig 0.17.0, 0.16.0 (default), 0.15.2 and 0.14.1, a checked subset only;\n" ++
  "see docs/support-matrix.md for versions, examples and open requirements.\n\n" ++
  "Example:\n" ++
  "  lake exe air2lean out -o MyGen.lean --namespace My --prefix myfile.\n\n" ++
  "To translate a Zig source file, use scripts/translate.sh instead.\n" ++
  "Check setup with scripts/doctor.sh; start with docs/getting-started.md.\n" ++
  "Generated definitions describe the program; properties need separate proofs."

structure Args where
  airDir : System.FilePath
  outPath : System.FilePath
  ns : String
  prefix_ : String
  /-- `--float-semantics` (default `ieee`; `docs/floats.md` §Semantics, `Air2Lean/Emit.lean`'s
  `FloatSemantics`). -/
  floatSemantics : FloatSemantics
  spawnSemantics : SpawnSemantics := .available
  profile : Option String
  modelRegistry : Option String
  registryTemplate : Bool := false
  proofApi : Bool := false
  /-- `--allow-unqualified-build-mode`: admit a profile outside `BuildProfile.qualifiedBuilds`
  (`docs/build-modes.md`); recorded in the generated header. -/
  allowUnqualified : Bool := false
  /-- `--timing-json`: per-phase timing report path (`docs/perf-budgets.md`). -/
  timingJson : Option String := none
  /-- `--source-map-json`: per-function source map sidecar (`docs/stable-generation.md`). -/
  sourceMapJson : Option String := none
  /-- `--split-modules`: the umbrella module name (`docs/modular-output.md`). -/
  splitModules : Option String := none
  /-- `--device-contract`: the declared device (`docs/volatile-effects.md`, L13). -/
  deviceContract : Option String := none
  /-- `--air-certificate`: AIR semantics certificate path (`docs/air-semantics.md`). -/
  airCertificate : Option String := none
  /-- `--air-certificate-import`: the Lean module of the `-o` output, for the certificate. -/
  airCertificateImport : Option String := none
  /-- `--allocator-model` (default `std`; `docs/allocator-model.md`). -/
  allocatorModel : AllocatorModel := .std

/-- Remove `--allocator-model V` (or `--allocator-model=V`) from `args`; at most once. -/
private def takeAllocatorModel (args : List String) :
    Except String (Option AllocatorModel × List String) := do
  let rec go (args : List String) (seen : Option AllocatorModel) (acc : List String) :
      Except String (Option AllocatorModel × List String) := do
    match args with
    | [] => pure (seen, acc.reverse)
    | ["--allocator-model"] => throw s!"missing value for --allocator-model\n{usage}"
    | "--allocator-model" :: v :: rest =>
      if seen.isSome then throw s!"duplicate --allocator-model\n{usage}"
      let mode ← (parseAllocatorModel v).mapError (fun message => s!"{message}\n{usage}")
      go rest (some mode) acc
    | a :: rest => go rest seen (a :: acc)
  go (splitAllocatorModelFlag args) none []

private partial def parseArgsGo (args : List String)
    (airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy : Option String)
    (registryTemplate : Bool) : Except String Args :=
  match args with
  | [] =>
    match airDir, outPath, ns with
    | some airDir, some outPath, some ns => do
      let spawning ← match spawnPolicy with
        | none => pure .available
        | some value => (parseSpawnPolicy value).mapError (fun message => s!"{message}\n{usage}")
      match floatSemantics with
      | none | some "ieee" => .ok { airDir, outPath, ns, prefix_ := prefix_.getD "", floatSemantics := .ieee, spawnSemantics := spawning, profile, modelRegistry, registryTemplate }
      | some "compiler-rt" => .ok { airDir, outPath, ns, prefix_ := prefix_.getD "", floatSemantics := .compilerRt, spawnSemantics := spawning, profile, modelRegistry, registryTemplate }
      | some other => .error s!"invalid --float-semantics '{other}' (want 'ieee' or 'compiler-rt')\n{usage}"
    | none, _, _ => .error s!"missing <air-dir>\n{usage}"
    | _, none, _ => .error s!"missing -o <out.lean>\n{usage}"
    | _, _, none => .error s!"missing --namespace <Ns>\n{usage}"
  | "-o" :: v :: rest => parseArgsGo rest airDir (some v) ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
  | "--namespace" :: v :: rest => parseArgsGo rest airDir outPath (some v) prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
  | "--prefix" :: v :: rest => parseArgsGo rest airDir outPath ns (some v) floatSemantics profile modelRegistry spawnPolicy registryTemplate
  | "--float-semantics" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ (some v) profile modelRegistry spawnPolicy registryTemplate
  | "--spawn-policy" :: v :: rest =>
    if spawnPolicy.isSome then .error s!"duplicate --spawn-policy\n{usage}"
    else parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry (some v) registryTemplate
  | "--profile" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ floatSemantics (some v) modelRegistry spawnPolicy registryTemplate
  | "--model-registry" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile (some v) spawnPolicy registryTemplate
  | "--proof-api" :: rest =>
    (parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate).map
      (fun a => { a with proofApi := true })
  | "--allow-unqualified-build-mode" :: rest =>
    (parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate).map
      (fun a => { a with allowUnqualified := true })
  | "--model-registry-template" :: rest => parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy true
  | "--timing-json" :: v :: rest => do
    let a ← parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    if a.timingJson.isSome then .error s!"duplicate --timing-json\n{usage}"
    else .ok { a with timingJson := some v }
  | "--source-map-json" :: v :: rest => do
    let a ← parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    if a.sourceMapJson.isSome then .error s!"duplicate --source-map-json\n{usage}"
    else .ok { a with sourceMapJson := some v }
  | "--split-modules" :: v :: rest => do
    let a ← parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    if a.splitModules.isSome then .error s!"duplicate --split-modules\n{usage}"
    else .ok { a with splitModules := some v }
  | "--device-contract" :: v :: rest => do
    let a ← parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    if a.deviceContract.isSome then .error s!"duplicate --device-contract\n{usage}"
    else .ok { a with deviceContract := some v }
  | "--air-certificate" :: v :: rest => do
    let a ← parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    if a.airCertificate.isSome then .error s!"duplicate --air-certificate\n{usage}"
    else .ok { a with airCertificate := some v }
  | "--air-certificate-import" :: v :: rest => do
    let a ← parseArgsGo rest airDir outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    if a.airCertificateImport.isSome then .error s!"duplicate --air-certificate-import\n{usage}"
    else .ok { a with airCertificateImport := some v }
  | ["--device-contract"] | ["-o"] | ["--namespace"] | ["--prefix"] | ["--float-semantics"] | ["--profile"] | ["--model-registry"] | ["--spawn-policy"] | ["--timing-json"] | ["--source-map-json"] | ["--split-modules"] | ["--air-certificate"] | ["--air-certificate-import"] =>
    .error s!"missing value for {args.head!}\n{usage}"
  | v :: rest =>
    if v.startsWith "-" then .error s!"unknown option: '{v}'\n{usage}"
    else if airDir.isNone then parseArgsGo rest (some v) outPath ns prefix_ floatSemantics profile modelRegistry spawnPolicy registryTemplate
    else .error s!"unexpected argument: '{v}'\n{usage}"

def parseArgs (args : List String) : Except String Args := do
  let (allocatorModel, args) ← takeAllocatorModel args
  let a ← parseArgsGo args none none none none none none none none false
  let a := { a with allocatorModel := allocatorModel.getD .std }
  if a.registryTemplate && a.modelRegistry.isSome then
    throw "--model-registry-template cannot be combined with --model-registry"
  if a.registryTemplate && a.spawnSemantics == .fallible then
    throw "--model-registry-template cannot be combined with --spawn-policy fallible"
  if a.timingJson == some a.outPath.toString then
    throw s!"--timing-json must not name the -o output '{a.outPath}'\n{usage}"
  if let some path := a.sourceMapJson then
    if path == a.outPath.toString || a.timingJson == some path then
      throw s!"--source-map-json must not name the -o output or the --timing-json report\n{usage}"
    if a.registryTemplate then
      throw "--source-map-json cannot be combined with --model-registry-template"
  if let some root := a.splitModules then
    if a.registryTemplate then
      throw "--split-modules cannot be combined with --model-registry-template"
    unless ModuleSplit.validRoot root do
      throw s!"invalid --split-modules '{root}': use a dot-separated module name, such as Proofs.Ex.Gen\n{usage}"
    -- The parts import each other by module name, so the umbrella must sit at that module's path.
    unless ModuleSplit.matchesOutput root a.outPath.toString do
      throw s!"--split-modules {root} needs -o ending in {root.replace "." "/"}.lean\n{usage}"
    let manifest := (ModuleSplit.manifestPath a.outPath).toString
    if a.timingJson == some manifest || a.sourceMapJson == some manifest then
      throw s!"--timing-json and --source-map-json must not name the module manifest {manifest}\n{usage}"
  if a.registryTemplate && a.deviceContract.isSome then
    throw "--device-contract cannot be combined with --model-registry-template"
  if a.airCertificate.isSome != a.airCertificateImport.isSome then
    throw s!"--air-certificate and --air-certificate-import go together\n{usage}"
  if let some path := a.airCertificate then
    if path == a.outPath.toString || a.timingJson == some path || a.sourceMapJson == some path then
      throw s!"--air-certificate must not name another output\n{usage}"
    if a.registryTemplate || a.modelRegistry.isSome then
      throw "--air-certificate cannot be combined with model registries"
  unless (a.ns.splitOn ".").all (fun part => !part.isEmpty && mangleField part == part) do
    throw s!"invalid --namespace '{a.ns}': use dot-separated Lean identifiers, such as My.Program\n{usage}"
  if let some p := a.profile then
    unless p == BuildProfile.legacyName || p == BuildProfile.currentName || p == BuildProfile.bigEndianName do
      throw s!"invalid --profile '{p}'\n{usage}"
  pure a

/-- Shared checked path for parsed AIR; metadata remains available to the CLI. -/
def processRaw (raw : Raw.RawFunc) : Except String Func := do
  let f ← normalize raw
  check f
  pure f

/-- Parse, normalize, and check one AIR JSON file's contents into a `Func`. -/
def processOne (contents : String) : Except String Func := do
  processRaw (← Raw.parseFile contents)

/-- Evaluate one pure stage between two monotonic clock reads; returns elapsed nanoseconds.
Observation only: the value is exactly `fn ()`. -/
@[noinline] private def timed (fn : Unit → α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let value ← IO.lazyPure fn
  let stop ← IO.monoNanosNow
  pure (value, stop - start)

/-- Per-phase totals for `--timing-json` (nanoseconds, summed over AIR files). -/
structure PhaseTimes where
  read : Nat := 0
  renumber : Nat := 0
  parse : Nat := 0
  normalize : Nat := 0
  check : Nat := 0
  emit : Nat := 0
  write : Nat := 0

private def writeTiming (path : String) (t : PhaseTimes) (files functions inputBytes outputBytes : Nat) :
    IO Unit := do
  let ns (n : Nat) : Lean.Json := Lean.toJson n
  let report := Lean.Json.mkObj [("schema", .str "air2lean-timing/1"),
    ("files", ns files), ("functions", ns functions),
    ("input_bytes", ns inputBytes), ("output_bytes", ns outputBytes),
    ("phases_ns", Lean.Json.mkObj [("read", ns t.read), ("renumber", ns t.renumber),
      ("parse", ns t.parse), ("normalize", ns t.normalize), ("check", ns t.check),
      ("emit", ns t.emit), ("write", ns t.write)])]
  try IO.FS.writeFile path (report.compress ++ "\n") catch e =>
    throw (IO.userError s!"writing timing report {path}: {e}")

def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => die e
  | .ok a =>
    let entries ← try a.airDir.readDir catch e =>
      throw (IO.userError s!"reading AIR directory {a.airDir}: {e}")
    let jsonPaths :=
      ((entries.filter fun e => e.fileName.endsWith ".json").qsort
        (fun a b => decide (a.fileName < b.fileName))).map (·.path)
    if jsonPaths.isEmpty then
      die (s!"no *.json files found in {a.airDir}\n" ++
        "Export AIR with the patched Zig compiler first, or use scripts/translate.sh.\n" ++
        "Check the dump filter and make functions reachable with export fn or comptime references.")
    else
      let mut times : PhaseTimes := {}
      let readStart ← IO.monoNanosNow
      let texts ← jsonPaths.mapM fun path => do
        try StrictJson.readFile path catch e =>
          throw (IO.userError s!"reading AIR file {path}: {e}")
      let models ← match a.modelRegistry with
        | none => pure #[]
        | some path =>
          let contents ← StrictJson.readFile path
          match ModelRegistry.parse contents with
          | .ok models => pure models
          | .error error => throw (IO.userError error)
      let device ← match a.deviceContract with
        | none => pure none
        | some path =>
          match DeviceContract.parse (← StrictJson.readFile path) with
          | .ok contract => pure (some contract)
          | .error error => throw (IO.userError s!"{path}: {error}")
      times := { times with read := (← IO.monoNanosNow) - readStart }
      -- Preserve the historical <full name>.json emission order even when storage
      -- uses hashes or project staging names. Cache before anonymous renumbering.
      let ((originalNames, rewrittenTexts), renumberNs) ← timed fun _ => Anon.renumberAllWithNames texts
      times := { times with renumber := renumberNs }
      let mut profiles : Array BuildProfile := #[]
      let mut funcs : Array Func := #[]
      let mut err : Option String := none
      for (path, contents) in jsonPaths.zip rewrittenTexts do
        if err.isNone then
          -- Same stage order as `processRaw` (preflight, normalize, check), timed separately.
          let (parsed, parseNs) ← timed fun _ => Raw.parseFile contents a.allocatorModel
          times := { times with parse := times.parse + parseNs }
          match parsed with
          | .error e => err := some s!"{path}: {e}"
          | .ok raw =>
            profiles := profiles.push raw.profile
            let (normalized, normalizeNs) ← timed fun _ => (do
              if a.registryTemplate || !models.isEmpty then
                ModelRegistry.preflight raw.types raw.layouts
              normalize raw : Except String Func)
            times := { times with normalize := times.normalize + normalizeNs }
            match normalized with
            | .error e => err := some s!"{path}: {e}"
            | .ok f =>
              let (checkedOne, checkNs) ← timed fun _ => check f device
              times := { times with check := times.check + checkNs }
              match checkedOne with
              | .error e => err := some s!"{path}: {e}"
              | .ok () => funcs := funcs.push f
      let (checked, programNs) ← timed fun _ => (do
        match err with | some e => throw e | none => pure ()
        -- A template lists the extern calls that bind to no definition as model symbols.
        if a.registryTemplate then return (← resolveExternsCollect funcs models).1
        let resolved ← resolveExterns funcs models
        checkProgram resolved models profiles[0]?
        if a.spawnSemantics == .fallible then checkFallibleSpawnCalls resolved
        return resolved
        : Except String (Array Func))
      times := { times with check := times.check + programNs }
      let inputBytes := texts.foldl (fun n text => n + text.utf8ByteSize) 0
      match checked with
      | .error e => die e
      | .ok resolved =>
        funcs := resolved
        match BuildProfile.checkProgram profiles a.profile a.allowUnqualified with
        | .error e => die e
        | .ok profile =>
          if a.registryTemplate then
            match ModelRegistry.template profile funcs with
            | .error error => die error
            | .ok template =>
              IO.FS.writeFile a.outPath (template.pretty ++ "\n")
              if let some path := a.timingJson then
                writeTiming path times jsonPaths.size funcs.size inputBytes 0
              pure 0
          else
            -- Reads and every validation guard retain their original path order.
            -- Only successful emission depends on identity rather than storage keys. With
            -- content-addressed instances (docs/air-json.md §Instances), the renamed identity:
            -- the compiler's instance numbers must not order the definitions.
            let keyed := funcs.any (·.identities.any (·.instanceKey.isSome))
            let emissionKeys := (if keyed then funcs.map (·.name) else originalNames).map (· ++ ".json")
            let emissionFuncs := ((emissionKeys.zip funcs).qsort
              (fun a b => decide (a.1 < b.1))).map (·.2)
            let semantics := match a.floatSemantics with | .ieee => "ieee" | .compilerRt => "compiler-rt"
            -- An admission opt-in is part of the claim scope: the header records it.
            let admission := if a.allowUnqualified then
              [("admission", Lean.Json.str "unqualified-build-mode")] else []
            let admission := admission ++ if a.allocatorModel == .translated then
              [("allocator_model", Lean.Json.str "translated")] else []
            let metadata := Lean.Json.mkObj ([("profile", profile.toJson),
              ("float_semantics", .str semantics), ("correspondence", .str "model")] ++ admission)
            let header := "-- air2lean-profile: " ++ metadata.compress ++ "\n" ++
              (if models.isEmpty then "" else
                "-- air2lean-models: " ++ (ModelRegistry.report models).compress ++ "\n") ++
              (match device with
                | none => ""
                | some c => "-- air2lean-device: " ++ c.report.compress ++ "\n")
            let ((src, parts), emitNs) ← timed fun _ =>
              let parts := emitParts emissionFuncs a.prefix_ a.floatSemantics models a.spawnSemantics
                a.proofApi device
              (header ++ parts.render a.ns, parts)
            let declNames := parts.declNames
            times := { times with emit := emitNs }
            -- Fail closed (MM-6): an emitter placeholder means the checker let through input
            -- that has no translation; nothing is written.
            let kinds := placeholdersIn src
            unless kinds.isEmpty do
              return ← die s!"EMITTER_PLACEHOLDER: the input reached emitter arms that the checker \
                should exclude ({"; ".intercalate (kinds.extract 0 8).toList}); nothing was written. \
                This is a translator bug: please report the AIR input."
            -- Fail closed: a 32-bit translation uses only width-parameterized runtime names.
            if profile.pointerBits != 64 then
              if let some name := width64Leak src then
                throw (IO.userError s!"internal error: the {profile.pointerBits}-bit translation \
                  uses the 64-bit runtime name '{name}'")
            let writeStart ← IO.monoNanosNow
            match a.splitModules with
            | none =>
              try IO.FS.writeFile a.outPath src catch e =>
                throw (IO.userError s!"writing Lean output {a.outPath}: {e}")
            | some root =>
              -- The same parts as `src`, one module per call group (`Air2Lean/ModuleSplit.lean`).
              let stem := (a.outPath.fileName.getD "").dropEnd ".lean".length |>.toString
              let base := a.outPath.parent.getD "."
              let mods := ModuleSplit.modules parts a.ns root stem header
              ModuleSplit.write (base / stem) base mods
              let manifest := ModuleSplit.manifest a.ns root metadata translatorJson mods
              let manifestPath := ModuleSplit.manifestPath a.outPath
              try IO.FS.writeFile manifestPath (manifest.pretty ++ "\n") catch e =>
                throw (IO.userError s!"writing module manifest {manifestPath}: {e}")
            times := { times with write := (← IO.monoNanosNow) - writeStart }
            if let some path := a.timingJson then
              writeTiming path times jsonPaths.size funcs.size inputBytes src.utf8ByteSize
            if let (some path, some genModule) := (a.airCertificate, a.airCertificateImport) then
              let cert := Certificate.emit emissionFuncs a.ns declNames genModule
              try IO.FS.writeFile path cert catch e =>
                throw (IO.userError s!"writing AIR certificate {path}: {e}")
            if let some path := a.sourceMapJson then
              -- Path order matches `funcs`: every file reached emission. Records follow
              -- the same identity order as emission.
              let entries := ((emissionKeys.zip (jsonPaths.zip (originalNames.zip (rewrittenTexts.zip funcs)))).qsort
                (fun x y => decide (x.1 < y.1))).map (·.2)
              let declOf : Std.HashMap String String := declNames.foldl (fun m (k, v) => m.insert k v) {}
              let records ← entries.mapM fun (airPath, airName, text, f) => do
                let doc ← match StrictJson.parse text with
                  | .ok doc => pure doc
                  | .error e => throw (IO.userError s!"{airPath}: {e}")
                let definition := declOf.getD f.name f.name
                let api := if a.proofApi then some (proofLemmaIndex f) else none
                pure (SourceMap.record doc airName (airPath.fileName.getD airPath.toString) definition api)
              let spawn := match a.spawnSemantics with | .available => "available" | .fallible => "fallible"
              let sidecar := Lean.Json.mkObj [("format", .str "air2lean-source-map-v2"),
                ("namespace", .str a.ns), ("metadata", metadata),
                ("translator", translatorJson),
                ("options", Lean.Json.mkObj ([("spawn_policy", .str spawn),
                  ("models", if models.isEmpty then .null else ModelRegistry.report models)] ++
                  (match device with | none => [] | some c => [("device", c.report)]))),
                ("functions", .arr records)]
              try IO.FS.writeFile path (sidecar.compress ++ "\n") catch e =>
                throw (IO.userError s!"writing source map {path}: {e}")
            pure 0

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--diagnostics-json" then
    Diagnostics.runCheck args
  else if args == ["--print-op-table"] then
    IO.println opTableJson.pretty
    pure 0
  else if args == ["--help"] || args == ["-h"] then
    IO.println help
    pure 0
  else
    try run args catch e => die e.toString

end Air2Lean

def main (args : List String) : IO UInt32 := Air2Lean.main args
