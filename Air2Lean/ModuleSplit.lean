import Air2Lean.Emit
import Lean.Data.Json

/-!
# Modular output (`--split-modules`)

`air2lean AIR -o Proofs/Ex/Gen.lean --namespace Ex --split-modules Proofs.Ex.Gen` writes the
same declarations as the single-file output, split along the call graph
(`docs/modular-output.md`):

* `<Root>.Types` (`Gen/Types.lean`): the imports and everything the functions share: types,
  inline assembly, models, globals and `Tgt`;
* one module per call group (`callGroups`, a strongly connected component of the call graph),
  `<Root>.F_<declaration>` (`Gen/F_<declaration>.lean`). It imports `<Root>.Types` and the
  modules of the groups it calls, so an edit to one group rebuilds only that module and the
  modules that import it, transitively;
* `<Root>.Dispatch` (`Gen/Dispatch.lean`), only for programs with spawn targets;
* the umbrella `-o` file, which imports them all. Every module uses the same `namespace`, so
  an `import <Root>` sees exactly the declarations of the single-file output.

Each group's text is the single-file text of that group, so the definitions are identical.
`Gen.modules.json` beside the umbrella (`air2lean-module-split-v2`) lists every module with its functions,
declarations and imports, and the translator revision (`Air2Lean/Revision.lean`) that wrote
them; `scripts/module-split.py` derives invalidation keys from it.
-/

namespace Air2Lean.ModuleSplit
open Lean

def format : String := "air2lean-module-split-v2"

/-- First line of every generated part: stale parts carrying it are removed on the next run. -/
def marker : String := "-- air2lean-split-part"

structure Module where
  name : String
  /-- Relative to the umbrella's directory. -/
  file : String
  /-- `types`, `group`, `dispatch` or `umbrella`. -/
  kind : String
  functions : Array String := #[]
  definitions : Array String := #[]
  imports : Array String
  text : String

/-- A module name: dot-separated ASCII identifiers, none a Lean keyword. -/
def validRoot (root : String) : Bool :=
  (root.splitOn ".").all fun part => !leanKeywords.contains part && match part.toList with
    | c :: cs => c.isAlpha && c.toNat < 128 && cs.all fun c => c.toNat < 128 && (c.isAlphanum || c == '_')
    | [] => false

/-- The umbrella file must be exactly `<root as a path>.lean`, possibly under a source directory:
`MyGen.lean` does not hold module `Gen`. -/
def matchesOutput (root out : String) : Bool :=
  let path := root.replace "." "/" ++ ".lean"
  out == path || out.endsWith ("/" ++ path)

/-- The manifest written beside the umbrella `out` (`Gen.lean` → `Gen.modules.json`). -/
def manifestPath (out : System.FilePath) : System.FilePath :=
  out.withExtension "modules.json"

/-- `F_` and the declaration name with every non-ASCII-identifier character replaced by `_`,
at most 100 characters. Uniqueness is case-insensitive (`allocate`). -/
def component (decl : String) : String :=
  "F_" ++ String.ofList ((plainName decl).toList.take 100 |>.map fun c =>
    if c.toNat < 128 && (c.isAlphanum || c == '_') then c else '_')

/-- Assign module components in the order of each group's least declaration name, so a
name depends only on the set of declarations, not on emission order. -/
def allocate (reps : Array String) : Array String := Id.run do
  let order := (reps.zipIdx.qsort fun a b => decide (a.1 < b.1))
  let mut taken : Std.HashSet String := {}
  let mut out : Array String := reps.map fun _ => ""
  for (rep, i) in order do
    let base := component rep
    let mut name := base
    let mut k := 2
    while taken.contains name.toLower do
      name := s!"{base}_{k}"
      k := k + 1
    taken := taken.insert name.toLower
    out := out.set! i name
  return out

private def render (imports : Array String) (ns : String) (body : List String)
    (opens : List String := []) : String :=
  String.intercalate "\n" (marker :: imports.toList.map ("import " ++ ·)) ++ "\n\n" ++
    String.intercalate "\n\n" ([s!"namespace {ns}"] ++ opens ++ body ++ [s!"end {ns}"]) ++ "\n"

/-- The modules of `parts` under `root`, whose directory is `stem` (the umbrella's file name
without `.lean`). The umbrella comes last; `header` is its profile comment. -/
def modules (parts : EmitParts) (ns root stem header : String) : Array Module := Id.run do
  let declOf : Std.HashMap String String := parts.declNames.foldl (fun m (k, v) => m.insert k v) {}
  let decl (source : String) := declOf.getD source source
  let reps := parts.groups.map fun (members, _, _) =>
    (members.map decl).foldl (fun acc d => if acc.isEmpty || d < acc then d else acc) ""
  let names := allocate reps
  let groupOf : Std.HashMap String String := (parts.groups.zip names).foldl (init := {})
    fun m ((members, _, _), name) => members.foldl (fun m s => m.insert s s!"{root}.{name}") m
  let typesName := s!"{root}.Types"
  let importsOf (callees : Array String) : Array String :=
    #[typesName] ++ ((callees.filterMap (groupOf[·]?)).qsort (· < ·) |> dedupNames)
  let headerImports := parts.header.filterMap fun line => (line.dropPrefix? "import ").map (·.toString)
  let comments := parts.header.filter (!·.startsWith "import ")
  let mut out := #[{
    name := typesName, file := s!"{stem}/Types.lean", kind := "types"
    imports := headerImports.toArray
    text := render headerImports.toArray ns (comments ++ parts.preamble) parts.opens : Module }]
  for ((members, callees, text), name) in parts.groups.zip names do
    out := out.push {
      name := s!"{root}.{name}", file := s!"{stem}/{name}.lean", kind := "group"
      functions := members, definitions := members.map decl
      imports := importsOf callees
      text := render (importsOf callees) ns [text] parts.opens }
  if !parts.dispatch.isEmpty then
    let imports := importsOf parts.dispatchTargets
    out := out.push {
      name := s!"{root}.Dispatch", file := s!"{stem}/Dispatch.lean", kind := "dispatch"
      definitions := #["dispatch"], imports, text := render imports ns parts.dispatch parts.opens }
  let all := out.map (·.name)
  out := out.push {
    name := root, file := s!"{stem}.lean", kind := "umbrella", imports := all
    text := header ++ String.intercalate "\n" (all.toList.map ("import " ++ ·)) ++ "\n" }
  return out

/-- `translator`: the revision object of the source-map sidecar (`lean`, `revision`, `modules`),
so every module key is bound to the translator that wrote the parts. -/
def manifest (ns root : String) (metadata translator : Json) (mods : Array Module) : Json :=
  let strs (a : Array String) : Json := .arr (a.map Json.str)
  Json.mkObj [("format", .str format), ("namespace", .str ns), ("root", .str root),
    ("metadata", metadata), ("translator", translator),
    ("modules", .arr (mods.map fun m => Json.mkObj [("module", .str m.name),
      ("file", .str m.file), ("kind", .str m.kind), ("functions", strs m.functions),
      ("definitions", strs m.definitions), ("imports", strs m.imports)]))]

/-- Write each module whose text changed; remove stale marked parts from `dir`. -/
def write (dir : System.FilePath) (base : System.FilePath) (mods : Array Module) : IO Unit := do
  IO.FS.createDirAll dir
  let wanted := mods.map fun m => (base / m.file).normalize
  for entry in ← dir.readDir do
    if entry.fileName.endsWith ".lean" && !wanted.contains entry.path.normalize then
      let first := ((← IO.FS.readFile entry.path).splitOn "\n").head!
      if first == marker then IO.FS.removeFile entry.path
  for m in mods do
    let path := base / m.file
    let same ← try pure ((← IO.FS.readFile path) == m.text) catch _ => pure false
    unless same do
      try IO.FS.writeFile path m.text catch e =>
        throw (IO.userError s!"writing Lean module {path}: {e}")

end Air2Lean.ModuleSplit
