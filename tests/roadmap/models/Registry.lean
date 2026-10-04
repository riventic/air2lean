import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Air2Lean Lean
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error error => throw (IO.userError error)

private def expectError {α : Type} (result : Except String α) (part : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"expected error containing {part}")
  | .error message => require (decide ((message.splitOn part).length > 1)) message

def main (args : List String) : IO Unit := do
  let directory : System.FilePath ← match args with
    | [] => pure "tests/roadmap/models"
    | [output] => pure (System.FilePath.mk output)
    | _ => throw (IO.userError "usage: Registry.lean [output-directory]")
  IO.FS.createDirAll directory
  let raw ← get <| Raw.parseFile (← IO.FS.readFile "tests/roadmap/models/client.json")
  let f ← get <| normalize raw
  let template ← get <| ModelRegistry.template raw.profile #[f]
  let entry := ((template.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let obj ← get entry.getObj?
  let entry := Json.mkObj <| obj.toArray.toList ++ [
    ("import", .str "tests.roadmap.models.Model"),
    ("implementation", .str "RegistryExample.identity"),
    ("contract", .str "RegistryExample.contract"), ("trust", .str "proved"),
    ("proof", .str "RegistryExample.evidence"), ("termination", .str "total"),
    ("errors", .arr #[]), ("effects", .str "preserves"), ("dependencies", .arr #[])]
  let document := Json.mkObj [("schema", toJson (1 : Nat)), ("models", .arr #[entry])]
  let models ← get <| ModelRegistry.parse document.compress
  let _ ← get <| ModelRegistry.check models raw.profile #[f]
  let _ ← get <| checkProgram #[f] models (some raw.profile)
  require (checkProgram #[f] models).toOption.isNone "binding without checked profile"
  require (checkProgram #[f]).toOption.isNone "unregistered external call"
  require ((memoryFunctions #[f] (models.map (·.symbol))).contains "client") "external memory propagation"
  require (ModelRegistry.check (models ++ models) raw.profile #[f]).toOption.isNone "duplicate symbols"
  require (ModelRegistry.check models {raw.profile with zigVersion := "0.15.2"} #[f]).toOption.isNone "version mismatch"
  require (ModelRegistry.check models raw.profile #[{f with types := f.types.set! 0 (.int false 16)}]).toOption.isNone "signature mismatch"
  require (ModelRegistry.check #[{models[0]! with ret := .str "wrong"}] raw.profile #[f]).toOption.isNone "return mismatch"
  require (ModelRegistry.check models raw.profile #[{f with layouts := f.layouts.set! 0 {size := some 2, align := some 2}}]).toOption.isNone "layout mismatch"
  require (ModelRegistry.check models raw.profile #[{f with name := "project.identity"}]).toOption.isNone "AIR override"
  require (ModelRegistry.parse "{\"schema\":2,\"models\":[]}").toOption.isNone "future registry schema"
  expectError (ModelRegistry.parse "{\"schema\":1e1000000000,\"models\":[]}") "exponent exceeds"
  expectError (ModelRegistry.parse "{\"schema\":1,\"schema\":1,\"models\":[]}") "duplicate JSON object key"
  let nested (n : Nat) := String.join (List.replicate n "[") ++ "0" ++ String.join (List.replicate n "]")
  let _ ← get <| StrictJson.parse (nested 128)
  expectError (StrictJson.parse (nested 129)) "JSON nesting exceeds"
  let _ ← get <| StrictJson.parse (nested ModelRegistry.maxJsonDepth) ModelRegistry.maxJsonDepth
  expectError (ModelRegistry.parse (nested (ModelRegistry.maxJsonDepth + 1))) "JSON nesting exceeds"
  let oversized ← try
    let _ ← StrictJson.readBounded (fun _ => pure (ByteArray.mk #[0, 0, 0])) 2
    pure false
  catch _ => pure true
  require oversized "bounded registry reader rejects growth"
  let source := emit #[f] "ExternalClient" "" .ieee models
  require (decide ((source.splitOn "def client (p0 : BitVec 8) : Zig.MemM").length > 1)) "client uses MemM"
  require (decide ((source.splitOn "theorem air2lean_model_0_evidence").length > 1)) "proved obligation"
  require ((source.splitOn "axiom air2lean_model_0_evidence").length == 1) "proved binding has no generated assumption"
  IO.FS.writeFile (directory / "registry.json") (document.pretty ++ "\n")
  IO.FS.writeFile (directory / "Generated.lean") (source ++ "\n" ++
    "namespace ExternalClient\n" ++
    "theorem client_result {x before result after}\n" ++
    "    (run : client x before = some (.ok (result, after))) : result = x := by\n" ++
    "  have modelRun : RegistryExample.identity x before = some (.ok (result, after)) := by\n" ++
    "    change (some (Except.ok (x, before)) = some (Except.ok (result, after))) at run\n" ++
    "    change (some (Except.ok (x, before)) = some (Except.ok (result, after)))\n" ++
    "    exact run\n" ++
    "  exact (air2lean_model_0_contract.success air2lean_model_0_evidence (by trivial) modelRun).1\n" ++
    "end ExternalClient\n")
  let diamond : Array Ty := (Array.range 21).map fun i =>
    if i == 0 then .int false 8 else .tuple #[i - 1, i - 1]
  let budgetError := (ModelRegistry.preflight diamond #[]).toOption.isNone
  require budgetError "shared DAG rejected before exponential expansion"
  let small := diamond.extract 0 5
  let _ ← get <| ModelRegistry.preflight small #[]
  require (ModelRegistry.preflight #[.ptr "one" false 0] #[]).toOption.isNone "pointer signature cycle"
  -- A previously memoized subtree must count its full height beneath a later root.
  let chain : Array Ty := (Array.range 261).map fun i =>
    if i == 0 then .int false 8 else .optional (i - 1)
  let _ ← get <| ModelRegistry.typeShapes chain #[] #[255]
  expectError (ModelRegistry.typeShapes chain #[] #[256]) "signature nesting exceeds"
  expectError (ModelRegistry.typeShapes chain #[] #[128, 257]) "signature nesting exceeds"
  expectError (ModelRegistry.typeShapes chain #[] #[257, 128]) "signature nesting exceeds"
  let tupleChain := chain.push (.tuple #[130, 260])
  expectError (ModelRegistry.typeShapes tupleChain #[] #[130, 261]) "signature nesting exceeds"
  expectError (ModelRegistry.typeShapes #[.int false 8] #[] (Array.replicate 6000 0)) "expanded signature budget"
  let duplicateValues := ModelRegistry.valueTypeIndex f.types
    #[{id := 9, ty := 0, op := .arg 0}, {id := 9, ty := 1, op := .arg 0}]
  require ((← get <| ModelRegistry.argumentTypeIds duplicateValues #[.inst 9]) == #[0]) "first argument type occurrence"
  let indexed := (ModelRegistry.callIndex #[
    {f with body := #[{id := 10, ty := 0, op := .call (.func "project.identity" false none) #[.inst 1]},
      {id := 11, ty := 0, op := .call (.func "project.identity" false none) #[.inst 2]}]}, f]).getD "project.identity" #[]
  require (indexed.size == 3) "all matching calls indexed"
  require (indexed.map (·.functionIndex) == #[0, 0, 1]) "function traversal order"
  require ((indexed.map (·.args))[0]? == some #[.inst 1] &&
    (indexed.map (·.args))[1]? == some #[.inst 2]) "instruction traversal order"
  let repeated : Array Val := Array.replicate 6000 (.inst 0)
  expectError (ModelRegistry.check models raw.profile #[{f with body := #[
    {id := 0, ty := 0, op := .arg 0},
    {id := 1, ty := 0, op := .call (.func "project.identity" false none) repeated}]}]) "expanded signature budget"
  let selectionFuncs := #[
    {f with name := "unrelated", body := #[]},
    {f with body := #[
      {id := 0, ty := 0, op := .arg 0},
      {id := 10, ty := 0, op := .call (.func "project.identity" false none) #[.inst 0]},
      {id := 11, ty := 0, op := .call (.func "project.identity" false none) #[.int 0 7]},
      {id := 12, ty := 0, op := .call (.func "project.other" false none) #[.inst 0]}]}, f]
  let selectionModels := models.push {models[0]! with symbol := "project.other"}
  let first := firstModelCalls selectionModels selectionFuncs
  let exhaustive := ModelRegistry.callIndex selectionFuncs
  for m in selectionModels do
    let summary (site : ModelRegistry.CallSite) := (site.functionIndex, site.args, site.ret)
    require ((first[m.symbol]?.map summary) ==
      (((exhaustive.getD m.symbol #[])[0]?).map summary)) "emitter/checker first-site equivalence"
  require (first.size == 2 && (first["project.identity"]?.map (·.functionIndex)) == some 1) "registered first sites only"
  let deepTypes : Array Ty := ((Array.range 65).map fun i =>
    if i == 0 then Ty.int false 8 else Ty.optional (i - 1)).push .noreturn
  let deepFunc := {f with params := #[64], ret := 64, types := deepTypes, layouts := #[], body := #[
    {id := 0, ty := 64, op := .arg 0},
    {id := 1, ty := 64, op := .call (.func "project.identity" false none) #[.inst 0]},
    {id := 2, ty := 65, op := .ret (.inst 1)}]}
  let deepTemplate ← get <| ModelRegistry.template raw.profile #[deepFunc]
  let deepEntry := ((deepTemplate.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let deepEntry := entry.setObjVal! "signature" (deepEntry.getObjValD "signature")
  let deepEntry := (deepEntry.setObjVal! "implementation" (.str "RegistryExample.polyIdentity"))
    |>.setObjVal! "contract" (.str "RegistryExample.polyContract")
    |>.setObjVal! "proof" (.str "RegistryExample.polyEvidence")
  let deepDocument := document.setObjVal! "models" (.arr #[deepEntry])
  let deepModels ← get <| ModelRegistry.parse deepDocument.compress
  let _ ← get <| ModelRegistry.check deepModels raw.profile #[deepFunc]
  let collisionFunc := {f with name := "collisionClient", params := #[], ret := 2,
    types := f.types.push (.struct "p0" "auto" #[("value", 0)]),
    layouts := f.layouts.push {size := some 1, align := some 1, offsets := #[0]}, body := #[
      {id := 0, ty := 2, op := .call (.func "project.identity" false none) #[.undef 2]},
      {id := 1, ty := 1, op := .ret (.inst 0)}]}
  let (collisionParams, collisionReturn) ← get <| ModelRegistry.signature collisionFunc #[.undef 2] 2
  let collisionModels := #[{models[0]! with params := collisionParams, ret := collisionReturn,
    implementation := "RegistryExample.polyIdentity", contract := "RegistryExample.polyContract",
    proof := some "RegistryExample.polyEvidence"}]
  let _ ← get <| check collisionFunc
  let _ ← get <| checkProgram #[collisionFunc] collisionModels (some raw.profile)
  let collisionSource := emit #[collisionFunc] "CollisionClient" "" .ieee collisionModels
  require (decide ((collisionSource.splitOn "(p0 : p0_air2lean1)").length > 1)) "model binder reserves aggregate name"
  let ordinaryCollision := emit #[collisionFunc] "CollisionClient" ""
  require (decide ((ordinaryCollision.splitOn "structure p0 where").length > 1)) "ordinary declaration names unchanged"
  IO.FS.writeFile (directory / "CollisionGenerated.lean") (collisionSource ++ "\n" ++
    "namespace CollisionClient\n" ++
    "theorem client_result {before result after}\n" ++
    "    (run : collisionClient before = some (.ok (result, after))) : result = (default : p0_air2lean1) := by\n" ++
    "  have modelRun : RegistryExample.polyIdentity (default : p0_air2lean1) before = some (.ok (result, after)) := by\n" ++
    "    change (some (Except.ok ((default : p0_air2lean1), before)) = some (Except.ok (result, after))) at run\n" ++
    "    change (some (Except.ok ((default : p0_air2lean1), before)) = some (Except.ok (result, after)))\n" ++
    "    exact run\n" ++
    "  exact (air2lean_model_0_contract.success air2lean_model_0_evidence (by trivial) modelRun).1\n" ++
    "end CollisionClient\n")
  let tupleRaw ← get <| Raw.parseFile (← IO.FS.readFile "tests/roadmap/models/tuple-client.json")
  let tupleFunc ← get <| normalize tupleRaw
  let _ ← get <| check tupleFunc
  let tupleTemplate ← get <| ModelRegistry.template tupleRaw.profile #[tupleFunc]
  let tupleEntry := ((tupleTemplate.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let tupleFields ← get tupleEntry.getObj?
  let tupleEntry := Json.mkObj <| tupleFields.toArray.toList ++ [
    ("import", .str "tests.roadmap.models.Model"),
    ("implementation", .str "RegistryExample.tupleSelect"),
    ("contract", .str "RegistryExample.tupleContract"), ("trust", .str "proved"),
    ("proof", .str "RegistryExample.tupleEvidence"), ("termination", .str "total"),
    ("errors", .arr #[]), ("effects", .str "preserves"), ("dependencies", .arr #[])]
  let tupleDocument := Json.mkObj [("schema", toJson (1 : Nat)), ("models", .arr #[tupleEntry])]
  let tupleModels ← get <| ModelRegistry.parse tupleDocument.compress
  let _ ← get <| checkProgram #[tupleFunc] tupleModels (some tupleRaw.profile)
  let tupleSource := emit #[tupleFunc] "TupleClient" "" .ieee tupleModels
  require (decide ((tupleSource.splitOn "Contract ((BitVec 8 × BitVec 8) × (BitVec 8))").length > 1)) "tuple argument grouping"
  IO.FS.writeFile (directory / "tuple-registry.json") (tupleDocument.pretty ++ "\n")
  IO.FS.writeFile (directory / "TupleGenerated.lean") (tupleSource ++ "\n" ++
    "namespace TupleClient\n" ++
    "theorem client_result {x y before result after}\n" ++
    "    (run : tupleClient x y before = some (.ok (result, after))) : result = x.1 := by\n" ++
    "  have modelRun : RegistryExample.tupleSelect (x, y) before = some (.ok (result, after)) := by\n" ++
    "    change (some (Except.ok (x.1, before)) = some (Except.ok (result, after))) at run\n" ++
    "    change (some (Except.ok (x.1, before)) = some (Except.ok (result, after)))\n" ++
    "    exact run\n" ++
    "  exact (air2lean_model_0_contract.success air2lean_model_0_evidence (by trivial) modelRun).1\n" ++
    "end TupleClient\n")
  IO.println "model registry tests passed; generated typed client obligation"
