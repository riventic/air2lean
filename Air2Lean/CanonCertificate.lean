import Air2Lean.CanonSem
import Air2Lean.Air.Normalize
import Air2Lean.Air.Anon

/-!
Per-run certificates for the final debug-definition-ID rewrite. The theorem is about
the two reified normalized snapshots, relative to `Sem`; normalization, reification,
live-ID renumbering and emission retain their existing trust boundaries.
-/

namespace Air2Lean.CanonCertificate

-- Structural derivation includes every constructor and every Func field. In particular,
-- this does not use the emission certificate printer's smaller operation fragment.
deriving instance Repr for Op, SwitchCase, Inst
deriving instance Repr for Func
deriving instance BEq for Global

def printFunc (f : Func) : String := (repr f).pretty 100

/-- Bound each literal's elaboration depth; concatenate larger arrays as a balanced tree. -/
private partial def arrayRangeTerm (terms : Array Std.Format) (start stop : Nat) : Std.Format :=
  if stop - start ≤ 32 then
    Std.Format.bracket "#[" (Std.Format.joinSep (terms.extract start stop).toList
      ("," ++ Std.Format.line)) "]"
  else
    let middle := start + (stop - start) / 2
    Std.Format.paren (arrayRangeTerm terms start middle ++ " ++" ++ Std.Format.line ++
      arrayRangeTerm terms middle stop)

private def arrayTerm (terms : Array Std.Format) : Std.Format :=
  arrayRangeTerm terms 0 terms.size

private def recordTerm (fields : List (String × Std.Format)) : Std.Format :=
  Std.Format.bracket "{ " (Std.Format.joinSep
    (fields.map fun (name, value) => Std.Format.text name ++ " := " ++ Std.Format.nest 2 value)
    ("," ++ Std.Format.line)) " }"

private def appTerm (name : String) (args : List Std.Format) : Std.Format :=
  Std.Format.group (Std.Format.text name ++ Std.Format.nest 2
    (Std.Format.line ++ Std.Format.joinSep (args.map Std.Format.paren) Std.Format.line))

/-- Sharing is purely structural: keys select candidates, and every reuse also checks the
complete typed value. Definition counts keep names unique even when keys collide. -/
private structure SharedPool (α : Type) where
  typeName : String
  stem : String
  entries : Std.HashMap String (Array (α × String)) := {}
  definitions : Array String := #[]

private def SharedPool.intern [BEq α] (pool : SharedPool α) (key : String)
    (value : α) (render : Unit → String) : String × SharedPool α := Id.run do
  let key := pool.typeName ++ ":" ++ key
  let candidates := pool.entries[key]?.getD #[]
  for (previous, name) in candidates do
    if previous == value then return (name, pool)
  let name := s!"{pool.stem}_{pool.definitions.size}"
  return (name, { pool with
    entries := pool.entries.insert key (candidates.push (value, name))
    definitions := pool.definitions.push s!"def {name} : {pool.typeName} :=\n{render ()}\n" })

/-- The same interner shares elements and arrays without changing table order or indices. -/
private def internTable [BEq α] [Repr α] (values : Array α)
    (elements : SharedPool α) (arrays : SharedPool (Array α)) :
    String × SharedPool α × SharedPool (Array α) := Id.run do
  let mut elements := elements
  let mut names := #[]
  for value in values do
    let text := (repr value).pretty 100
    let (name, updated) := elements.intern text value (fun _ => text)
    elements := updated
    names := names.push name
  let (name, arrays) := arrays.intern (",".intercalate names.toList) values
    (fun _ => (arrayTerm (names.map Std.Format.text)).pretty 100)
  return (name, elements, arrays)

private structure BodyPrinter where
  stem : String
  nextId : Nat := 0
  definitions : Array String := #[]
  deriving Inhabited

mutual

/-- Nested bodies get their own literal definitions, so syntax depth does not accumulate
across blocks. The root and every child use the same bounded array representation. -/
private partial def bodyDefinition (name : String) (body : Array Inst) : StateM BodyPrinter Unit := do
  let terms ← body.mapM fun i => do
    let op ← match i.op with
      | .block b => pure (appTerm "Air2Lean.Op.block" [← nestedBody b])
      | .loop b => pure (appTerm "Air2Lean.Op.loop" [← nestedBody b])
      | .condBr v t e =>
        pure (appTerm "Air2Lean.Op.condBr" [repr v, ← nestedBody t, ← nestedBody e])
      | .switchBr v cs e =>
        pure (appTerm "Air2Lean.Op.switchBr" [repr v, ← caseTerms cs, ← nestedBody e])
      | .loopSwitchBr v cs e =>
        pure (appTerm "Air2Lean.Op.loopSwitchBr" [repr v, ← caseTerms cs, ← nestedBody e])
      | .«try» v b => pure (appTerm "Air2Lean.Op.«try»" [repr v, ← nestedBody b])
      | .tryPtr v b => pure (appTerm "Air2Lean.Op.tryPtr" [repr v, ← nestedBody b])
      | op => pure (repr op)
    return recordTerm [("id", repr i.id), ("ty", repr i.ty), ("op", op)]
  modify fun state => { state with
    definitions := state.definitions.push s!"def {name} : Array Inst :=\n{(arrayTerm terms).pretty 100}\n" }

private partial def nestedBody (body : Array Inst) : StateM BodyPrinter Std.Format := do
  let state ← get
  let name := s!"{state.stem}_part_{state.nextId}"
  set { state with nextId := state.nextId + 1 }
  bodyDefinition name body
  return Std.Format.text name

private partial def caseTerms (cases : Array SwitchCase) : StateM BodyPrinter Std.Format := do
  let terms ← cases.mapM fun c => do
    return recordTerm [("items", repr c.items), ("ranges", repr c.ranges),
      ("body", ← nestedBody c.body)]
  return arrayTerm terms

end

/-- Emit the actual snapshots, sharing their unchanged non-body fields. The caller supplies
a valid Lean namespace. `checkDirectory` independently checks the parsed printed snapshots
against fresh normalization of the translation's actual input directory. -/
def emit (snapshots : Array (Nat × Func × Func)) (ns : String) : Except String String := do
  let mut lines := #["import Air2Lean.CanonCertificate", "",
    "-- Generated by air2lean --canon-certificate; scripts/gen-integrity.py owns freshness.",
    "-- Only debug definition IDs are certified, relative to Air2Lean.Sem.",
    s!"namespace {ns}", "", "open Air2Lean", ""]
  let mut typeValues : SharedPool Ty := { typeName := "Ty", stem := "shared_ty" }
  let mut typeArrays : SharedPool (Array Ty) := { typeName := "Array Ty", stem := "shared_types" }
  let mut layoutValues : SharedPool Layout := { typeName := "Layout", stem := "shared_layout" }
  let mut layoutArrays : SharedPool (Array Layout) := { typeName := "Array Layout", stem := "shared_layouts" }
  let mut globalValues : SharedPool Global := { typeName := "Global", stem := "shared_global" }
  let mut globalArrays : SharedPool (Array Global) := { typeName := "Array Global", stem := "shared_globals" }
  let mut functions := #[]
  for ((offset, before, after), k) in snapshots.zipIdx do
    let mapped := { before with body := DebugIds.mapDebugArray (fun id => id - offset) before.body }
    unless printFunc mapped == printFunc after do
      throw s!"{after.name}: normalized debug-ID snapshots do not match the actual Raw renumber offset"
    let (types, updatedTypeValues, updatedTypeArrays) := internTable after.types typeValues typeArrays
    typeValues := updatedTypeValues
    typeArrays := updatedTypeArrays
    let (layouts, updatedLayoutValues, updatedLayoutArrays) := internTable after.layouts layoutValues layoutArrays
    layoutValues := updatedLayoutValues
    layoutArrays := updatedLayoutArrays
    let (globals, updatedGlobalValues, updatedGlobalArrays) := internTable after.globals globalValues globalArrays
    globalValues := updatedGlobalValues
    globalArrays := updatedGlobalArrays
    let (_, bodies) := (bodyDefinition s!"before_body_{k}" before.body).run { stem := s!"before_body_{k}" }
    functions := functions ++ #[
      s!"def metadata_base_{k} : Func :=\n{printFunc { after with body := #[], types := #[], layouts := #[], globals := #[] }}\n",
      s!"def metadata_{k} : Func := \{ metadata_base_{k} with types := {types}, layouts := {layouts}, globals := {globals} }\n",
      s!"def offset_{k} : Nat := {offset}\n"] ++ bodies.definitions ++ #[
      s!"def after_body_{k} : Array Inst :=\n  DebugIds.mapDebugArray (fun id => id - offset_{k}) before_body_{k}\n",
      s!"def after_{k} : Func := \{ metadata_{k} with body := after_body_{k} }\n",
      s!"def before_{k} : Func := \{ metadata_{k} with body := before_body_{k} }\n",
      s!"theorem erased_{k} : DebugIds.eraseBody before_body_{k}.toList =",
      s!"    DebugIds.eraseBody after_body_{k}.toList :=",
      s!"  DebugIds.erase_mapDebugArray (fun id => id - offset_{k}) before_body_{k}", "",
      s!"theorem preserves_{k} (call : Sem.Oracle) (args : List Sem.Value) :",
      s!"    Sem.execFunc call before_{k} args = Sem.execFunc call after_{k} args :=",
      s!"  DebugIds.execFunc_of_body_erase_eq call metadata_{k} _ _ args erased_{k}", ""]
  lines := lines ++ typeValues.definitions ++ typeArrays.definitions ++
    layoutValues.definitions ++ layoutArrays.definitions ++
    globalValues.definitions ++ globalArrays.definitions ++ functions
  let entries := (Array.range snapshots.size).map fun k => s!"(offset_{k}, before_{k}, after_{k})"
  lines := lines ++ #["def snapshots : Array (Nat × Func × Func) :=",
    "  #[" ++ ", ".intercalate entries.toList ++ "]", "", s!"end {ns}", ""]
  return "\n".intercalate lines.toList

/-- Compare every field and the offset, returning whether any actual debug ID changed.
This is native binding evidence, not a kernel proof of decoding or serialization. -/
def checkSnapshots (actual snapshots : Array (Nat × Func × Func)) : IO Bool := do
  unless actual.size == snapshots.size do
    throw (IO.userError s!"canonicalization snapshot count differs: {actual.size} / {snapshots.size}")
  let mut changed := false
  for ((offset, before, after), (printedOffset, printedBefore, printedAfter)) in actual.zip snapshots do
    let beforeText := printFunc before
    let afterText := printFunc after
    unless offset == printedOffset && beforeText == printFunc printedBefore &&
        afterText == printFunc printedAfter do
      throw (IO.userError s!"{after.name}: canonicalization snapshots differ from decoded inputs")
    changed := changed || beforeText != afterText
  return changed

/-- Native serialization round trip. Input files have exactly the ordering and anonymous-name
rewrite used by Main. -/
def checkDirectory (dir : System.FilePath) (allocatorModel : AllocatorModel)
    (snapshots : Array (Nat × Func × Func)) : IO Bool := do
  let entries ← dir.readDir
  let paths := ((entries.filter (·.fileName.endsWith ".json")).qsort
    (fun a b => decide (a.fileName < b.fileName))).map (·.path)
  let texts ← paths.mapM StrictJson.readFile
  let (_, texts) := Anon.renumberAllWithNames texts
  let errorTable ← readErrorTable dir
  let actual ← texts.mapM fun text => IO.ofExcept do
    let (offset, before, after) ← normalizeDebugTrace (← Raw.parseFile text allocatorModel)
    return (offset, ← withErrorTable before errorTable, ← withErrorTable after errorTable)
  checkSnapshots actual snapshots

end Air2Lean.CanonCertificate
