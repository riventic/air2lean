import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-!
# CLI

`air2lean <air-dir> -o <out.lean> --namespace <Ns> [--prefix <p>]` reads every `*.json` file in
`<air-dir>` (`docs/air-json.md`), parses + normalizes + checks each into a `Func`
(`Air2Lean/Air/{Json,Normalize}.lean`, `Air2Lean/Check.lean`), then emits them all as one Lean
file (`Air2Lean/Emit.lean`) importing `ZigLean`, under `namespace <Ns>`.

Exits 1 with a message on any error at any stage: a bad flag, an unparsable/unsupported AIR
file, or a function outside the checked subset.
-/

namespace Air2Lean

def usage : String :=
  "usage: air2lean <air-dir> -o <out.lean> --namespace <Ns> [--prefix <p>] " ++
    "[--float-semantics ieee|compiler-rt]"

structure Args where
  airDir : System.FilePath
  outPath : System.FilePath
  ns : String
  prefix_ : String
  /-- `--float-semantics` (default `ieee`; `docs/floats.md` §Semantics, `Air2Lean/Emit.lean`'s
  `FloatSemantics`). -/
  floatSemantics : FloatSemantics

private partial def parseArgsGo (args : List String)
    (airDir outPath ns prefix_ floatSemantics : Option String) : Except String Args :=
  match args with
  | [] =>
    match airDir, outPath, ns with
    | some airDir, some outPath, some ns =>
      match floatSemantics with
      | none | some "ieee" => .ok { airDir, outPath, ns, prefix_ := prefix_.getD "", floatSemantics := .ieee }
      | some "compiler-rt" => .ok { airDir, outPath, ns, prefix_ := prefix_.getD "", floatSemantics := .compilerRt }
      | some other => .error s!"invalid --float-semantics '{other}' (want 'ieee' or 'compiler-rt')\n{usage}"
    | none, _, _ => .error s!"missing <air-dir>\n{usage}"
    | _, none, _ => .error s!"missing -o <out.lean>\n{usage}"
    | _, _, none => .error s!"missing --namespace <Ns>\n{usage}"
  | "-o" :: v :: rest => parseArgsGo rest airDir (some v) ns prefix_ floatSemantics
  | "--namespace" :: v :: rest => parseArgsGo rest airDir outPath (some v) prefix_ floatSemantics
  | "--prefix" :: v :: rest => parseArgsGo rest airDir outPath ns (some v) floatSemantics
  | "--float-semantics" :: v :: rest => parseArgsGo rest airDir outPath ns prefix_ (some v)
  | ["-o"] | ["--namespace"] | ["--prefix"] | ["--float-semantics"] =>
    .error s!"missing value for {args.head!}\n{usage}"
  | v :: rest =>
    if airDir.isNone then parseArgsGo rest (some v) outPath ns prefix_ floatSemantics
    else .error s!"unexpected argument: '{v}'\n{usage}"

def parseArgs (args : List String) : Except String Args :=
  parseArgsGo args none none none none none

/-- Parse, normalize, and check one AIR JSON file's contents into a `Func`. -/
def processOne (contents : String) : Except String Func := do
  let raw ← Raw.parseFile contents
  let f ← normalize raw
  check f
  pure f

def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => die e
  | .ok a =>
    let entries ← a.airDir.readDir
    let jsonPaths :=
      ((entries.filter fun e => e.fileName.endsWith ".json").qsort
        (fun a b => decide (a.fileName < b.fileName))).map (·.path)
    if jsonPaths.isEmpty then
      die s!"no *.json files found in {a.airDir}"
    else
      let mut funcs : Array Func := #[]
      let mut err : Option String := none
      for path in jsonPaths do
        if err.isNone then
          let contents ← IO.FS.readFile path
          match processOne contents with
          | .error e => err := some s!"{path}: {e}"
          | .ok f => funcs := funcs.push f
      match err with
      | some e => die e
      | none =>
        let src := emit funcs a.ns a.prefix_ a.floatSemantics
        IO.FS.writeFile a.outPath src
        pure 0

end Air2Lean

def main (args : List String) : IO UInt32 := Air2Lean.main args
