import Air2Lean.Emit
import Air2Lean.Diagnose

/-! The post-emission backstop of MM-6 (`docs/architecture-audit/memory-model.md`): emission
that reaches a `placeholder` arm fails closed. The function below bypasses `check` (which
rejects it, `test_cli.py`), as a checker gap would. Run: `lake env lean --run Gate.lean`. -/
open Air2Lean

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- `@reduce(.Add, v)` on a `@Vector(2, bool)`: the emitter has no term for it. -/
private def reduceBoolAdd : Func := {
  dialect := .ofVersion .v0_16_0
  name := "gate.reduceBoolAdd"
  params := #[2]
  ret := 0
  types := #[.bool, .noreturn, .vector 2 0]
  layouts := Array.replicate 3 {}
  globals := #[]
  body := #[
    { id := 0, ty := 2, op := .arg 0 },
    { id := 1, ty := 0, op := .reduce .add (.inst 0) },
    { id := 2, ty := 1, op := .ret (.inst 1) }] }

def main : IO Unit := do
  require (!(check reduceBoolAdd).isOk) "check accepts an arithmetic @reduce of bools"
  let raw := emit #[reduceBoolAdd] "Gate" "gate."
  require (placeholdersIn raw == #["arithmetic @reduce of a bool vector"])
    s!"unchecked emission did not mark the arm: {placeholdersIn raw}"
  require ((raw.splitOn "panic!").length == 1 && (raw.splitOn "pure default").length == 1)
    "an emitter arm still writes a term that succeeds in the logic"
  match emitWithNamesChecked #[reduceBoolAdd] "Gate" "gate." with
  | .ok _ => throw (IO.userError "emitWithNamesChecked wrote a placeholder")
  | .error e => require (e.startsWith "EMITTER_PLACEHOLDER:") s!"unexpected error: {e}"
  -- A placeholder-free program passes the gate unchanged.
  let fine : Func := { reduceBoolAdd with
    name := "gate.reduceBoolOr"
    body := reduceBoolAdd.body.modify 1 fun i => { i with op := .reduce .or (.inst 0) } }
  require (check fine).isOk "check rejects an @reduce(.Or) of bools"
  match emitWithNamesChecked #[fine] "Gate" "gate." with
  | .ok (src, _) => require (src == emit #[fine] "Gate" "gate.") "the gate changed the output"
  | .error e => throw (IO.userError s!"the gate rejected a checked program: {e}")
  IO.println "emitter placeholder gate: placeholder output rejected, checked output unchanged"
