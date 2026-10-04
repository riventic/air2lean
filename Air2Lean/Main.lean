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
    "[--float-semantics ieee|compiler-rt] [--spawn-policy available|fallible]"

structure Args where
  airDir : System.FilePath
  outPath : System.FilePath
  ns : String
  prefix_ : String
  /-- `--float-semantics` (default `ieee`; `docs/floats.md` §Semantics, `Air2Lean/Emit.lean`'s
  `FloatSemantics`). -/
  floatSemantics : FloatSemantics
  spawnSemantics : SpawnSemantics

private partial def parseArgsGo (args : List String)
    (airDir outPath ns prefix_ floatSemantics spawnSemantics : Option String) : Except String Args :=
  match args with
  | [] =>
    match airDir, outPath, ns with
    | some airDir, some outPath, some ns => do
      let floats ← match floatSemantics with
        | none | some "ieee" => pure FloatSemantics.ieee
        | some "compiler-rt" => pure FloatSemantics.compilerRt
        | some other => throw s!"invalid --float-semantics '{other}' (want 'ieee' or 'compiler-rt')\n{usage}"
      let spawning ← match spawnSemantics with
        | none | some "available" => pure SpawnSemantics.available
        | some "fallible" => pure SpawnSemantics.fallible
        | some other => throw s!"invalid --spawn-policy '{other}' (want 'available' or 'fallible')\n{usage}"
      pure {
        airDir := airDir
        outPath := outPath
        ns := ns
        prefix_ := prefix_.getD ""
        floatSemantics := floats
        spawnSemantics := spawning
      }
    | none, _, _ => .error s!"missing <air-dir>\n{usage}"
    | _, none, _ => .error s!"missing -o <out.lean>\n{usage}"
    | _, _, none => .error s!"missing --namespace <Ns>\n{usage}"
  | "-o" :: v :: rest => parseArgsGo rest airDir (some v) ns prefix_ floatSemantics spawnSemantics
  | "--namespace" :: v :: rest => parseArgsGo rest airDir outPath (some v) prefix_ floatSemantics spawnSemantics
  | "--prefix" :: v :: rest => parseArgsGo rest airDir outPath ns (some v) floatSemantics spawnSemantics
  | "--float-semantics" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ (some v) spawnSemantics
  | "--spawn-policy" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ floatSemantics (some v)
  | ["-o"] | ["--namespace"] | ["--prefix"] | ["--float-semantics"] | ["--spawn-policy"] =>
    .error s!"missing value for {args.head!}\n{usage}"
  | v :: rest =>
    if airDir.isNone then parseArgsGo rest (some v) outPath ns prefix_ floatSemantics spawnSemantics
    else .error s!"unexpected argument: '{v}'\n{usage}"

def parseArgs (args : List String) : Except String Args := do
  let a ← parseArgsGo args none none none none none none
  unless (a.ns.splitOn ".").all (fun part => !part.isEmpty && mangleField part == part) do
    throw s!"invalid --namespace '{a.ns}': use dot-separated Lean identifiers, such as My.Program\n{usage}"
  pure a

/-- Parse, normalize, and check one AIR JSON file's contents into a `Func`. -/
def processOne (contents : String) : Except String Func := do
  let raw ← Raw.parseFile contents
  let f ← normalize raw
  check f
  pure f

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
      let mut funcs : Array Func := #[]
      let mut err : Option String := none
      for (path, contents) in jsonPaths.zip (Anon.renumberAll texts) do
        if err.isNone then
          match processOne contents with
          | .error e => err := some s!"{path}: {e}"
          | .ok f => funcs := funcs.push f
      let checked := do
        match err with | some e => throw e | none => pure ()
        checkProgram funcs
        if a.spawnSemantics == SpawnSemantics.fallible then checkFallibleSpawnCalls funcs
      match checked with
      | .error e => die e
      | .ok () =>
        let src := emit funcs a.ns a.prefix_ a.floatSemantics a.spawnSemantics
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
