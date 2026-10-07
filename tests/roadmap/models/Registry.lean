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

private def provedEntry (entry : Json) (implementation contract proof : String) : Except String Json := do
  let obj ← entry.getObj?
  pure <| Json.mkObj <| obj.toArray.toList ++ [
    ("import", .str "tests.roadmap.models.Model"),
    ("implementation", .str implementation),
    ("contract", .str contract), ("trust", .str "proved"),
    ("proof", .str proof), ("termination", .str "total"),
    ("errors", .arr #[]), ("effects", .str "preserves"), ("dependencies", .arr #[])]

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
  let entry ← get <| provedEntry entry "RegistryExample.identity" "RegistryExample.contract" "RegistryExample.evidence"
  expectError (provedEntry (.str "scalar") "Model.impl" "Model.contract" "Model.proof") "object expected"
  let document := Json.mkObj [("schema", toJson (1 : Nat)), ("models", .arr #[entry])]
  let models ← get <| ModelRegistry.parse document.compress
  let _ ← get <| ModelRegistry.check models raw.profile #[f]
  let _ ← get <| checkProgram #[f] models (some raw.profile)
  -- Changing only the known sentinel byte must invalidate the binding. Both the
  -- parameter and return shapes include it, while legacy None keeps its old shape.
  let sentinelTypes : Array Ty := #[.int false 8, .noreturn, .ptr "slice" false 0]
  let sentinelLayouts : Array Layout := #[{size := some 1, align := some 1}, {},
    {size := some 16, align := some 8, ptrAlign := some 1, sentinel := true, sentinelByte := some 0}]
  let sentinelFunc : Func := { f with
    name := "sentinelClient"
    params := #[2]
    ret := 2
    types := sentinelTypes
    layouts := sentinelLayouts
    body := #[{id := 0, ty := 2, op := .arg 0},
      {id := 1, ty := 2, op := .call (.func "project.identity" false none) #[.inst 0]},
      {id := 2, ty := 1, op := .ret (.inst 1)}]
  }
  let sentinelTemplate ← get <| ModelRegistry.template raw.profile #[sentinelFunc]
  let sentinelEntry := ((sentinelTemplate.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let sentinelEntry ← get <| provedEntry sentinelEntry "RegistryExample.polyIdentity" "RegistryExample.polyContract" "RegistryExample.polyEvidence"
  let sentinelDocument := document.setObjVal! "models" (.arr #[sentinelEntry])
  let sentinelModels ← get <| ModelRegistry.parse sentinelDocument.compress
  let _ ← get <| checkProgram #[sentinelFunc] sentinelModels (some raw.profile)
  let byte42 := { sentinelFunc with layouts := sentinelLayouts.set! 2 {sentinelLayouts[2]! with sentinelByte := some 42} }
  let missingByte := { sentinelFunc with layouts := sentinelLayouts.set! 2 {sentinelLayouts[2]! with sentinelByte := none} }
  expectError (ModelRegistry.check sentinelModels raw.profile #[byte42]) "incompatible signature/layout"
  expectError (ModelRegistry.check sentinelModels raw.profile #[missingByte]) "incompatible signature/layout"
  let (zeroParams, zeroReturn) ← get <| ModelRegistry.signature sentinelFunc #[.inst 0] 2
  let (byteParams, byteReturn) ← get <| ModelRegistry.signature byte42 #[.inst 0] 2
  let (legacyParams, legacyReturn) ← get <| ModelRegistry.signature missingByte #[.inst 0] 2
  require (zeroParams != byteParams && zeroReturn != byteReturn &&
    zeroParams != legacyParams && zeroReturn != legacyReturn) "sentinel signature mutation erased exact or missing byte"
  require (((legacyReturn.getObjValD "layout").getObjVal? "sentinel_byte").toOption.isNone)
    "legacy missing-byte signature shape changed"
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
  let deepFunc : Func := { f with
    params := #[64]
    ret := 64
    types := deepTypes
    layouts := #[]
    body := #[
      {id := 0, ty := 64, op := .arg 0},
      {id := 1, ty := 64, op := .call (.func "project.identity" false none) #[.inst 0]},
      {id := 2, ty := 65, op := .ret (.inst 1)}]
  }
  let deepTemplate ← get <| ModelRegistry.template raw.profile #[deepFunc]
  let deepEntry := ((deepTemplate.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let deepEntry ← get <| provedEntry deepEntry "RegistryExample.polyIdentity" "RegistryExample.polyContract" "RegistryExample.polyEvidence"
  let deepDocument := document.setObjVal! "models" (.arr #[deepEntry])
  let deepModels ← get <| ModelRegistry.parse deepDocument.compress
  let _ ← get <| ModelRegistry.check deepModels raw.profile #[deepFunc]
  let collisionFunc : Func := { f with
    name := "collisionClient"
    params := #[]
    ret := 2
    types := f.types.push (.struct "p0" "auto" #[("value", 0)])
    layouts := f.layouts.push {size := some 1, align := some 1, offsets := #[0]}
    body := #[
      {id := 0, ty := 2, op := .call (.func "project.identity" false none) #[.undef 2]},
      {id := 1, ty := 1, op := .ret (.inst 0)}]
  }
  let (collisionParams, collisionReturn) ← get <| ModelRegistry.signature collisionFunc #[.undef 2] 2
  let collisionModel : ModelBinding := { models[0]! with
    params := collisionParams
    ret := collisionReturn
    implementation := "RegistryExample.polyIdentity"
    contract := "RegistryExample.polyContract"
    proof := some "RegistryExample.polyEvidence"
  }
  let collisionModels := #[collisionModel]
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
  let tupleEntry ← get <| provedEntry tupleEntry "RegistryExample.tupleSelect" "RegistryExample.tupleContract" "RegistryExample.tupleEvidence"
  require (!(entry.getObjValD "signature" == tupleEntry.getObjValD "signature")) "scalar/tuple signatures remain distinct"
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
  -- E01 footprints: `fill(buf: []u8, value: u8)` writes only its buffer's block.
  let fillTypes : Array Ty := #[.int false 8, .noreturn, .ptr "slice" false 0, .void]
  let fillFunc : Func := { f with
    name := "fillClient"
    params := #[2, 2, 0, 0]
    ret := 3
    types := fillTypes
    layouts := #[{size := some 1, align := some 1}, {},
      {size := some 16, align := some 8, ptrAlign := some 1}, {size := some 0, align := some 1}]
    body := #[{id := 0, ty := 2, op := .arg 0}, {id := 1, ty := 2, op := .arg 1},
      {id := 2, ty := 0, op := .arg 2}, {id := 3, ty := 0, op := .arg 3},
      {id := 4, ty := 3, op := .call (.func "project.fill" false none) #[.inst 0, .inst 2]},
      {id := 5, ty := 3, op := .call (.func "project.fill" false none) #[.inst 1, .inst 3]},
      {id := 6, ty := 1, op := .ret .void}]
  }
  let _ ← get <| check fillFunc
  let fillTemplate ← get <| ModelRegistry.template raw.profile #[fillFunc]
  let fillBase := ((fillTemplate.getObjValD "models").getArr?.toOption.getD #[])[0]!
  let fillEntry (effects : String) (footprint : Json) : Except String Json := do
    pure <| Json.mkObj <| (← fillBase.getObj?).toArray.toList ++ [
      ("import", .str "tests.roadmap.models.Fill"), ("implementation", .str "FillExample.fill"),
      ("contract", .str "FillExample.contract"), ("trust", .str "proved"),
      ("proof", .str "FillExample.evidence"), ("termination", .str "total"),
      ("errors", .arr #[.str "illegal"]), ("effects", .str effects), ("dependencies", .arr #[]),
      ("footprint", footprint)]
  let fillDoc (entry : Json) : Json := Json.mkObj [("schema", toJson (1 : Nat)), ("models", .arr #[entry])]
  let footprintJson (reads writes : List Nat) : Json :=
    Json.mkObj [("reads", toJson reads), ("writes", toJson writes)]
  let fillDocument := fillDoc (← get <| fillEntry "tracked" (footprintJson [] [0]))
  let fillModels ← get <| ModelRegistry.parse fillDocument.compress
  require (fillModels[0]!.footprint == some {reads := #[], writes := #[0]}) "footprint parsed"
  let _ ← get <| checkProgram #[fillFunc] fillModels (some raw.profile)
  for (fp, effects, part) in [
      (footprintJson [] [2], "tracked", "is not a parameter"),
      (footprintJson [] [0, 0], "tracked", "duplicate footprint writes"),
      (footprintJson [0] [0], "tracked", "both read and write"),
      (footprintJson [] [0], "preserves", "preserves binding cannot declare"),
      (Json.mkObj [("reads", toJson ([] : List Nat))], "tracked", "property not found"),
      (Json.mkObj [("reads", toJson ([] : List Nat)), ("writes", toJson [0]), ("allocates", .bool true)],
        "tracked", "unsupported field 'allocates'")] do
    expectError (ModelRegistry.parse (fillDoc (← get <| fillEntry effects fp)).compress) part
  let scalarFootprint ← get <| ModelRegistry.parse (fillDoc (← get <| fillEntry "tracked" (footprintJson [1] [0]))).compress
  expectError (ModelRegistry.check scalarFootprint raw.profile #[fillFunc]) "footprint parameter 1 is not a pointer"
  let fillReport := ModelRegistry.report fillModels
  require ((((fillReport.getObjValD "bindings").getArrVal? 0).toOption.getD .null).getObjValD "footprint" ==
    footprintJson [] [0]) "report lists the declared footprint"
  require (fillReport.getObjValD "assumptions" == toJson ([] : List String)) "proved binding is not an assumption"
  let assumedFields := (← get <| (← get <| fillEntry "tracked" (footprintJson [] [0])).getObj?).toArray.toList
  let assumedEntry := Json.mkObj <| (assumedFields.filter (·.1 != "proof")).map fun (k, v) =>
    if k == "trust" then (k, .str "assumed") else (k, v)
  let assumedModels ← get <| ModelRegistry.parse (fillDoc assumedEntry).compress
  require ((ModelRegistry.report assumedModels).getObjValD "assumptions" == toJson ["project.fill"])
    "assumed binding is listed as an assumption"
  let fillSource := emit #[fillFunc] "FillClient" "" .ieee fillModels
  require (decide ((fillSource.splitOn "def air2lean_model_0_footprint").length > 1)) "footprint definition"
  require (decide ((fillSource.splitOn "Respects air2lean_model_0_footprint := _root_.FillExample.evidence").length > 1))
    "footprint obligation"
  let assumedSource := emit #[fillFunc] "FillClient" "" .ieee assumedModels
  require (decide ((assumedSource.splitOn "axiom air2lean_model_0_evidence").length > 1)) "assumed footprint axiom"
  IO.FS.writeFile (directory / "fill-registry.json") (fillDocument.pretty ++ "\n")
  let fillClient := "\n" ++
    "namespace FillClient\n" ++
    "theorem fillClient_eq (a c : Zig.Slice) (x y : BitVec 8) :\n" ++
    "    fillClient a c x y = FillExample.client FillExample.fill a c x y := by\n" ++
    "  funext before\n" ++
    "  simp [fillClient, FillExample.client, air2lean_model_0, Zig.callM, StateT.run'_eq]\n" ++
    "/-- Frame preservation through the registry-bound obligation and footprint. -/\n" ++
    "theorem fillClient_fills_both {a c : Zig.Slice} {x y : BitVec 8} {before after : Zig.Mem}\n" ++
    "    (separate : a.ptr.block ≠ c.ptr.block)\n" ++
    "    (run : fillClient a c x y before = some (.ok ((), after))) :\n" ++
    "    FillExample.Filled after a x ∧ FillExample.Filled after c y := by\n" ++
    "  rw [fillClient_eq] at run\n" ++
    "  exact FillExample.client_fills_both air2lean_model_0_evidence separate run\n" ++
    "end FillClient\n"
  -- The CLI's `-- air2lean-models:` marker feeds scripts/external-contracts.py.
  let marker (models : Array ModelBinding) := "-- air2lean-models: " ++ (ModelRegistry.report models).compress ++ "\n"
  IO.FS.writeFile (directory / "FillGenerated.lean") (marker fillModels ++ fillSource ++ fillClient)
  IO.FS.writeFile (directory / "FillAssumedGenerated.lean") (marker assumedModels ++ assumedSource ++ fillClient)
  IO.println "model registry tests passed; generated typed client obligation"
