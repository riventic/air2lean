import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Air2Lean Lean
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error error => throw (IO.userError error)

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
  let duplicateValues := ModelRegistry.valueTypeIndex f.types
    #[{id := 9, ty := 0, op := .arg 0}, {id := 9, ty := 1, op := .arg 0}]
  require ((← get <| ModelRegistry.argumentTypeIds duplicateValues #[.inst 9]) == #[0]) "first argument type occurrence"
  require (((ModelRegistry.callIndex #[f, f]).getD "project.identity" #[]).size == 2) "all matching calls indexed"
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
