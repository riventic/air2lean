import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Checked arg/load/ret functions exercised through public emitter APIs with omitted
cache fields. The driver writes complete Lean; the gate elaborates and runs it separately. -/
open Lean Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def input (name : String) (used : Bool) : Json :=
  let num (n : Nat) := toJson n
  let obj := Json.mkObj
  let node (id : Nat) (tag : String) (ty : Nat) (args : Array Json)
      (extra : List (String × Json)) :=
    obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr #[
      obj [("k", .str "int"), ("signed", .bool false), ("bits", num 8),
        ("abi_size", num 1), ("abi_align", num 1)],
      obj [("k", .str "ptr"), ("size", .str "one"), ("const", .bool false),
        ("child", num 0), ("ptr_align", num 1), ("abi_size", num 8), ("abi_align", num 8)],
      obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)],
      obj [("k", .str "noreturn")]]),
    ("params", toJson (#[1] : Array Nat)), ("ret", num (if used then 0 else 2)),
    ("body", .arr #[node 0 "arg" 1 #[] [("param", num 0)],
      node 1 "load" 0 #[obj [("inst", num 0)]] [],
      node 2 "ret" 3 #[if used then obj [("inst", num 1)]
        else obj [("ty", num 2), ("val", .str "{}")]] []])]

private def checked (name : String) (used : Bool) : IO Func := do
  match (do
    let f ← normalize (← Raw.parseFunc (input name used))
    check f
    checkProgram #[f]
    pure f : Except String Func) with
  | .ok f => pure f
  | .error e => throw (IO.userError e)

-- All required pre-cache fields are present; the cache defaults themselves are tested.
private def bareContext (fc : FCtx) : FCtx := {
  types := fc.types, structNames := fc.structNames, funcNames := fc.funcNames
  allocFields := fc.allocFields, places := fc.places, blockTys := fc.blockTys
  allInsts := fc.allInsts, brT := fc.brT, repT := fc.repT
  retTy := fc.retTy, fnName := fc.fnName, localsName := fc.localsName, exitName := fc.exitName
  floatSemantics := fc.floatSemantics, zigVersion := fc.zigVersion
  mem := fc.mem, memFuncs := fc.memFuncs, layouts := fc.layouts, escaping := fc.escaping }

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: CacheContexts.lean OUTPUT_FILE")
  let used ← checked "used" true
  let unused ← checked "unused" false
  let mut definitions : List String := []
  for f in [used, unused] do
    let prepared := mkFCtx f #[] #[] .ieee #[f.name] #[]
    let bare := bareContext prepared
    require prepared.instUses.isSome "normal context did not populate its usage cache"
    require bare.instUses.isNone "bare context did not retain the absent-cache default"
    let reads := f.name == "used"
    require (bare.isReferenced 1 == reads) "bare usage lookup differs from actual runtime uses"
    let some load := f.allInsts.find? (·.id == 1)
      | throw (IO.userError "validated fixture lost load")
    let (env, line) := emitScalar bare #[(0, "p0")] load
    require (env.any (·.1 == 1) == reads) "direct bare scalar emission lost a used load binding"
    let some line := line | throw (IO.userError "direct load emission vanished")
    require (((line.splitOn "Zig.loadDiscardBytes").length > 1) == !reads)
      "direct bare emission confused used and unused loads"
    require (emitStmts bare #[] f.body.toList == emitStmts prepared #[] f.body.toList)
      "public statement emission differs between bare and prepared contexts"
    let parts := emitOneFunction f #[] #[] .ieee #[f.name] #[] #[]
    let bareDef := emitFunctionDef bare bare.fnName bare.localsName bare.exitName f.params f.ret f.body false
    require (bareDef == parts.defn) "complete bare-context function changed generated semantics"
    definitions := definitions ++ parts.types ++ [bareDef]
  let generated := "import ZigLean\nnamespace BareLoads\n" ++
    String.intercalate "\n\n" definitions ++ "\nend BareLoads\n"
  require ((generated.splitOn "air2lean: unbound inst").length == 1)
    "bare-context generated return contains an unbound-instruction panic"
  IO.FS.writeFile output (generated ++ "\n" ++
"open Zig\nderiving instance DecidableEq for Except\nprivate def value (c : MemM α) := (c.run {}).run.map (·.map Prod.fst)\nprivate def readUsed (initialized : Bool) : MemM (BitVec 8) := do\n  let p ← alloc .heap 1 1\n  if initialized then store 1 p (17#8)\n  BareLoads.used p\nprivate def readUnused : MemM (Array Nat) := do\n  let p ← alloc .heap 1 1\n  BareLoads.unused p\n  pure ((← get).footprint.map (·.len))\nprivate def badUsed : MemM (BitVec 8) := do\n  let p ← alloc .heap 0 1\n  BareLoads.used p\nprivate def badUnused : MemM Unit := do\n  let p ← alloc .heap 0 1\n  BareLoads.unused p\ndef main : IO Unit := do\n  unless value (readUsed true) = some (.ok (17#8)) do\n    throw (IO.userError \"bare used load value lost or returned panic\")\n  unless value (readUsed false) = some (.error .unspecified) do\n    throw (IO.userError \"bare used load decoder removed\")\n  unless value readUnused = some (.ok #[1]) do\n    throw (IO.userError \"bare unused load lost access footprint\")\n  unless value badUsed = some (.error .illegal) do\n    throw (IO.userError \"bare used load lost bounds check\")\n  unless value badUnused = some (.error .illegal) do\n    throw (IO.userError \"bare unused load lost bounds check\")\n  IO.println \"bare/prepared load cache regressions passed\"\n")
