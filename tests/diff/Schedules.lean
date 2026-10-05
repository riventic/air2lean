import Concurrent
import ScheduleSearch

namespace ScheduleCLI
open Lean (Json)

private def parse {α : Type} (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def field (j : Json) (key : String) : IO Json := parse (j.getObjVal? key)

private def keys (j : Json) (allowed : List String) : IO Unit := do
  let object ← parse j.getObj?
  for (key, _) in object.toArray do
    unless allowed.contains key do throw (IO.userError s!"unknown field {key}")

private def boundedNat (j : Json) (key : String) (max : Nat) : IO Nat := do
  let n ← parse (← field j key).getNat?
  if n > max then throw (IO.userError s!"{key} exceeds {max}")
  pure n

private def prefixOf (j : Json) : IO (Array Nat) := do
  let a ← parse j.getArr?
  a.mapM fun x => parse x.getNat?

private def expectedCheck (expected : Json) (e : DiffTest.ScheduleExecution) : IO Unit := do
  keys expected ["line", "kind", "options"]
  -- Each supplied binding is exact; omitted bindings make no additional claim.
  if let .ok j := expected.getObjVal? "line" then
    let line ← parse j.getStr?
    unless line == e.observation.line do throw (IO.userError "replay expected line differs")
  if let .ok j := expected.getObjVal? "kind" then
    let kind ← parse j.getStr?
    unless kind == e.observation.kind.tag do throw (IO.userError "replay expected kind differs")
  if let .ok j := expected.getObjVal? "options" then
    let options ← prefixOf j
    unless options == e.options do throw (IO.userError "replay expected options differ")

/-- Read bounded bytes before UTF-8 decoding. Partial reads are not EOF; at the limit,
one additional byte distinguishes an exact-size request from an oversized request. -/
partial def readRequest (stream : IO.FS.Stream) (limit : Nat := 8 * 1024 * 1024) : IO String := do
  let rec collect (acc : ByteArray) : IO ByteArray := do
    let remaining := limit - acc.size
    let chunk ← stream.read (USize.ofNat (min 65536 (remaining + 1)))
    if chunk.isEmpty then return acc
    if chunk.size > remaining then throw (IO.userError "request exceeds byte limit")
    collect (acc ++ chunk)
  let bytes ← collect .empty
  match String.fromUTF8? bytes with
  | some text => pure text
  | none => throw (IO.userError "request is not valid UTF-8")

/-- One request, one JSON response; agreement and explored bounded trees are never proofs. -/
def execute (request : Json) : IO Json := do
  keys request ["schema", "mode", "example", "function", "input", "fuel", "node_cap", "prefix_cap", "prefix", "expected"]
  let schema ← boundedNat request "schema" 1
  unless schema == 1 do throw (IO.userError "unsupported schema")
  let mode ← parse (← field request "mode").getStr?
  unless mode == "replay" || mode == "enumerate" do throw (IO.userError "mode must be replay or enumerate")
  let ex ← parse (← field request "example").getStr?
  let fn ← parse (← field request "function").getStr?
  let input ← field request "input"
  let fuel ← boundedNat request "fuel" 100000
  let nodeCap ← boundedNat request "node_cap" 2000
  let prefixCap ← boundedNat request "prefix_cap" 4096
  let run ← DiffConcurrent.runner ex fn input fuel
  let common := [("schema", Lean.toJson (1 : Nat)), ("mode", Json.str mode),
    ("qualified", Lean.toJson false), ("fuel", Lean.toJson fuel),
    ("node_cap", Lean.toJson nodeCap), ("prefix_cap", Lean.toJson prefixCap)]
  if mode == "replay" then
    if nodeCap == 0 then throw (IO.userError "replay requires node_cap >= 1")
    let prefix ← prefixOf (← field request "prefix")
    let e ← parse (DiffTest.replaySchedule prefixCap run prefix)
    if let .ok expected := request.getObjVal? "expected" then expectedCheck expected e
    pure (Json.mkObj (common ++ [
      ("runs", Lean.toJson (1 : Nat)), ("truncated", Lean.toJson false),
      ("node_cap_reached", Lean.toJson false), ("prefix_cap_reached", Lean.toJson false),
      ("exploration_complete", Lean.toJson false),
      ("saw_no_result", Lean.toJson (e.observation.kind == .boundedNoResult)),
      ("executions", Json.arr #[e.metadata]),
      ("outcomes", Json.arr #[e.observation.metadata])]))
  else
    if (request.getObjVal? "prefix").isOk || (request.getObjVal? "expected").isOk then
      throw (IO.userError "prefix and expected are replay-only fields")
    let result := DiffTest.enumerateSchedules nodeCap prefixCap run
    let truncated := result.nodeCapReached || result.prefixCapReached
    pure (Json.mkObj (common ++ [
      ("runs", Lean.toJson result.executions.size), ("truncated", Lean.toJson truncated),
      ("node_cap_reached", Lean.toJson result.nodeCapReached),
      ("prefix_cap_reached", Lean.toJson result.prefixCapReached),
      ("exploration_complete", Lean.toJson (!truncated)),
      ("saw_no_result", Lean.toJson result.sawNoResult),
      ("executions", Json.arr (result.executions.map (·.metadata))),
      ("outcomes", Json.arr (result.outcomes.map (·.metadata)))]))
end ScheduleCLI

def main (args : List String) : IO UInt32 := do
  try
    let raw ← match args with
      | [] => ScheduleCLI.readRequest (← IO.getStdin)
      | [path] => IO.FS.withFile path .read fun handle =>
          ScheduleCLI.readRequest (IO.FS.Stream.ofHandle handle)
      | _ => throw (IO.userError "usage: schedules [request.json] (or JSON on stdin)")
    let request ← match Lean.Json.parse raw with
      | .ok j => pure j
      | .error e => throw (IO.userError e)
    let response ← ScheduleCLI.execute request
    (← IO.getStdout).putStrLn response.compress
    pure 0
  catch e =>
    let response := Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)),
      ("qualified", Lean.toJson false), ("error", Lean.Json.str e.toString)]
    (← IO.getStdout).putStrLn response.compress
    pure 1
