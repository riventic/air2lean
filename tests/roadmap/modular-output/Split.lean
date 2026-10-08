import Air2Lean
import Air2Lean.Check
import Air2Lean.ModuleSplit

/-! `--split-modules` API regressions (I04). Run from the repository root:
`lake env lean tests/roadmap/modular-output/Split.lean`. The author never invokes a compiler. -/
open Air2Lean Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

-- Module components: deterministic, ASCII identifiers, unique ignoring case.
#guard ModuleSplit.component "«weird name»" == "F_weird_name"
#guard ModuleSplit.component "sum" == "F_sum"
#guard ModuleSplit.allocate #["b", "B", "a"] == #["F_b_2", "F_B", "F_a"]
#guard ModuleSplit.allocate #["a", "B", "b"] == #["F_a", "F_B", "F_b_2"]
#guard ModuleSplit.allocate #["x_2", "x", "X"] == #["F_x_2_2", "F_x_2", "F_X"]
#guard ModuleSplit.validRoot "Proofs.Ex.Gen" && !ModuleSplit.validRoot "Proofs..Gen" &&
  !ModuleSplit.validRoot "Proofs.1Gen" && !ModuleSplit.validRoot "Proofs.Gén" &&
  !ModuleSplit.validRoot "Proofs.end.Gen"
#guard ModuleSplit.matchesOutput "Proofs.Ex.Gen" "Proofs/Ex/Gen.lean" &&
  ModuleSplit.matchesOutput "Ex.Gen" "/tmp/pkg/Ex/Gen.lean" &&
  !ModuleSplit.matchesOutput "Gen" "out/MyGen.lean" && !ModuleSplit.matchesOutput "Ex.Gen" "Ex/Gen.lean.bak"

private def load (dir : System.FilePath) : IO (Array Func) := do
  let paths := ((← dir.readDir).filter (·.fileName.endsWith ".json")).qsort
    (fun a b => decide (a.fileName < b.fileName))
  paths.mapM fun entry => do
    let text ← IO.FS.readFile entry.path
    match (do let f ← normalize (← Raw.parseFile text); check f; pure f : Except String Func) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"{entry.path}: {e}")

/-- The body of one generated part: the text between its `namespace` and `end` lines. -/
private def body (ns text : String) : IO String := do
  let some rest := (text.splitOn s!"namespace {ns}\n\n")[1]? | throw (IO.userError "no namespace")
  let some inner := (rest.splitOn s!"\n\nend {ns}\n")[0]? | throw (IO.userError "no end")
  pure inner

private def checkExample (ex ns : String) (dispatch : Bool) : IO Unit := do
  let funcs ← load s!"tests/golden/{ex}/air"
  let parts := emitParts funcs s!"{ex}."
  let single := (emitWithNames funcs ns s!"{ex}.").1
  require (parts.render ns == single) s!"{ex}: rendered parts differ from emitWithNames"
  let mods := ModuleSplit.modules parts ns "Demo.Gen" "Gen" "-- header\n"
  let some umbrella := mods.back? | throw (IO.userError "no umbrella")
  require (umbrella.kind == "umbrella" && umbrella.name == "Demo.Gen" &&
    umbrella.imports == (mods.pop.map (·.name))) s!"{ex}: umbrella must import every part"
  require (mods.any (·.kind == "dispatch") == dispatch) s!"{ex}: dispatch module presence"
  -- Concatenating the part bodies in manifest order gives the single-file body.
  let bodies ← (mods.pop.filter (·.kind != "types") |>.mapM fun m => body ns m.text)
  let some types := mods[0]? | throw (IO.userError "no types module")
  let typesBody ← if parts.preamble.isEmpty then pure [] else pure [← body ns types.text]
  let header := String.intercalate "\n\n" parts.header
  let rebuilt := String.intercalate "\n\n" ([header, s!"\nnamespace {ns}"] ++ typesBody ++
    bodies.toList ++ [s!"end {ns}"])
  require (rebuilt == single) s!"{ex}: parts do not reassemble the single-file output"
  -- Each group imports the types module and exactly the groups of its outside callees.
  let moduleOf (source : String) := (mods.find? (·.functions.contains source)).map (·.name)
  for ((members, callees, _), m) in parts.groups.zip (mods.filter (·.kind == "group")) do
    require (m.functions == members) s!"{ex}: group order differs"
    let expected := (#["Demo.Gen.Types"] ++ ((callees.filterMap moduleOf).qsort (· < ·))).toList.eraseDups
    require (m.imports.toList == expected) s!"{ex}: {m.name} imports {m.imports} want {expected}"
    require (m.imports.all fun i => i == "Demo.Gen.Types" ||
      (mods.findIdx? (·.name == i)).getD 0 < (mods.findIdx? (·.name == m.name)).getD 0)
      s!"{ex}: {m.name} imports a later module"

#eval do
  checkExample "recursion" "Recursion" false
  checkExample "pointers" "Pointers" false
  checkExample "layout" "Layout" false
  checkExample "threads" "Threads" true
