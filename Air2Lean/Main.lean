import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
import Air2Lean.Air.Anon

/-!
# CLI

`air2lean <air-dir> -o <out.lean> --namespace <Ns> [--prefix <p>]` reads every `*.json` file in
`<air-dir>` (`docs/air-json.md`), parses + normalizes + checks each into a `Func`
(`Air2Lean/Air/{Json,Normalize}.lean`, `Air2Lean/Check.lean`), then emits them all as one Lean
file (`Air2Lean/Emit.lean`) importing `ZigLean`, under `namespace <Ns>`. Before parsing, each
`__anon_<n>` of a generic instance gets a stable number (`Air2Lean/Air/Anon.lean`).

Exits 1 with a message on any error at any stage: a bad flag, an unparsable/unsupported AIR
file, or a function outside the checked subset.
-/

namespace Air2Lean

def usage : String :=
  "usage: air2lean <air-dir> -o <out.lean> --namespace <Ns> [--prefix <p>] " ++
    "[--float-semantics ieee|compiler-rt] [--profile legacy-abi64-le|abi64-le-v1]"

structure Args where
  airDir : System.FilePath
  outPath : System.FilePath
  ns : String
  prefix_ : String
  /-- `--float-semantics` (default `ieee`; `docs/floats.md` §Semantics, `Air2Lean/Emit.lean`'s
  `FloatSemantics`). -/
  floatSemantics : FloatSemantics
  profile : Option String

private partial def parseArgsGo (args : List String)
    (airDir outPath ns prefix_ floatSemantics profile : Option String) : Except String Args :=
  match args with
  | [] =>
    match airDir, outPath, ns with
    | some airDir, some outPath, some ns =>
      match floatSemantics with
      | none | some "ieee" => .ok { airDir, outPath, ns, prefix_ := prefix_.getD "", floatSemantics := .ieee, profile }
      | some "compiler-rt" => .ok { airDir, outPath, ns, prefix_ := prefix_.getD "", floatSemantics := .compilerRt, profile }
      | some other => .error s!"invalid --float-semantics '{other}' (want 'ieee' or 'compiler-rt')\n{usage}"
    | none, _, _ => .error s!"missing <air-dir>\n{usage}"
    | _, none, _ => .error s!"missing -o <out.lean>\n{usage}"
    | _, _, none => .error s!"missing --namespace <Ns>\n{usage}"
  | "-o" :: v :: rest => parseArgsGo rest airDir (some v) ns prefix_ floatSemantics profile
  | "--namespace" :: v :: rest => parseArgsGo rest airDir outPath (some v) prefix_ floatSemantics profile
  | "--prefix" :: v :: rest => parseArgsGo rest airDir outPath ns (some v) floatSemantics profile
  | "--float-semantics" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ (some v) profile
  | "--profile" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ floatSemantics (some v)
  | ["-o"] | ["--namespace"] | ["--prefix"] | ["--float-semantics"] | ["--profile"] =>
    .error s!"missing value for {args.head!}\n{usage}"
  | v :: rest =>
    if airDir.isNone then parseArgsGo rest (some v) outPath ns prefix_ floatSemantics profile
    else .error s!"unexpected argument: '{v}'\n{usage}"

def parseArgs (args : List String) : Except String Args := do
  let a ← parseArgsGo args none none none none none none
  unless (a.ns.splitOn ".").all (fun part => !part.isEmpty && mangleField part == part) do
    throw s!"invalid --namespace '{a.ns}': use dot-separated Lean identifiers, such as My.Program\n{usage}"
  if let some p := a.profile then
    unless p == BuildProfile.legacyName || p == BuildProfile.currentName do
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
      die s!"no *.json files found in {a.airDir}"
    else
      let texts ← jsonPaths.mapM fun path => do
        try IO.FS.readFile path catch e =>
          throw (IO.userError s!"reading AIR file {path}: {e}")
      -- Preserve the historical <full name>.json emission order even when storage
      -- uses hashes or project staging names. Cache before anonymous renumbering.
      let emissionKeys := texts.map fun text => Anon.fnName text ++ ".json"
      let mut profiles : Array BuildProfile := #[]
      let mut funcs : Array Func := #[]
      let mut err : Option String := none
      for (path, contents) in jsonPaths.zip (Anon.renumberAll texts) do
        if err.isNone then
          match Raw.parseFile contents with
          | .error e => err := some s!"{path}: {e}"
          | .ok raw =>
            profiles := profiles.push raw.profile
            match processRaw raw with
            | .error e => err := some s!"{path}: {e}"
            | .ok f => funcs := funcs.push f
      match (match err with | some e => Except.error e | none => checkProgram funcs) with
      | .error e => die e
      | .ok () =>
        match BuildProfile.checkProgram profiles a.profile with
        | .error e => die e
        | .ok profile =>
          -- Reads and every validation guard retain their original path order.
          -- Only successful emission depends on identity rather than storage keys.
          let emissionFuncs := ((emissionKeys.zip funcs).qsort
            (fun a b => decide (a.1 < b.1))).map (·.2)
          let semantics := match a.floatSemantics with | .ieee => "ieee" | .compilerRt => "compiler-rt"
          let metadata := Lean.Json.mkObj [("profile", profile.toJson),
            ("float_semantics", .str semantics), ("correspondence", .str "model")]
          let src := "-- air2lean-profile: " ++ metadata.compress ++ "\n" ++
            emit emissionFuncs a.ns a.prefix_ a.floatSemantics
          try IO.FS.writeFile a.outPath src catch e =>
            throw (IO.userError s!"writing Lean output {a.outPath}: {e}")
          pure 0

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    IO.println usage
    pure 0
  else
    try run args catch e => die e.toString

end Air2Lean

def main (args : List String) : IO UInt32 := Air2Lean.main args
