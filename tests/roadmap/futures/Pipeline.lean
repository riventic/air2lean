import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! C08 translator boundary for the committed futures AIR: the qualified future API is accepted
for Zig 0.16.0 only, a cancelation point other than `Io.checkCancel` reachable from a task is
rejected in a program with `Future.cancel`, and the generated text names the future model.
Run with `lake env lean --run tests/roadmap/futures/Pipeline.lean`. -/
open Air2Lean

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error error => throw (IO.userError error)
private def expectError {α : Type} (result : Except String α) (part : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"expected error containing {part}")
  | .error message => require (decide ((message.splitOn part).length > 1)) message

/-- Rename every call of `old` in `f` to `new`. -/
private partial def renameCalls (old new : String) (insts : Array Inst) : Array Inst :=
  insts.map fun i =>
    let op := match i.op with
      | .call (.func name nr sf) args => .call (.func (if name == old then new else name) nr sf) args
      | .block b => .block (renameCalls old new b)
      | op => op
    { i with op }

def main : IO Unit := do
  let dir : System.FilePath := "tests/roadmap/futures/air/0.16.0"
  let mut funcs : Array Func := #[]
  for entry in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    let raw ← get <| Raw.parseFile (← IO.FS.readFile entry.path)
    funcs := funcs.push (← get <| normalize raw)
  let _ ← get <| checkProgram funcs
  -- Version qualification: the future API is a Zig 0.16.0 model.
  expectError (checkProgram (funcs.map fun f => { f with zigVersion := "0.15.2" }))
    "qualified Zig 0.16.0"
  -- Cancelation points: with `Future.cancel` in the program, a task may only observe a request
  -- at `Io.checkCancel`; a cancelable futex wait would observe it in std but not in the model.
  let cancelable := funcs.map fun f =>
    if f.name == "futures.cancellable" then
      { f with body := renameCalls "Io.checkCancel" "Io.futexWait" f.body } else f
  expectError (checkFutureCancelation cancelable) "is a cancelation point that the model does not deliver"
  -- Without a `Future.cancel` the same task is accepted by this rule.
  let noCancel := cancelable.filter (·.name != "futures.cancelValue")
  let _ ← get <| checkFutureCancelation noCancel
  -- The emitted program uses the future model and the generated targets.
  let text := emit funcs "Futures" "futures."
  for part in ["Zig.asyncC", "Zig.awaitC", "Zig.cancelC", "Zig.checkCancelC",
      "Zig.Future.complete futureSlot futureResult", "| square_future (futureSlot : Zig.Ptr)"] do
    require (decide ((text.splitOn part).length > 1)) s!"generated text lacks {part}"
  let fallible := emit funcs "Futures" "futures." (spawnSemantics := .fallible)
  require (decide ((fallible.splitOn "Zig.asyncWithPolicyC").length > 1)) "fallible policy not emitted"
  IO.println "futures translator boundary passed"
