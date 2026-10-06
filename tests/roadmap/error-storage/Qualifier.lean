import Air2Lean
import Air2Lean.Check
open Air2Lean

private def get (out : Except String α) : IO α := match out with
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)
private def reject (f : Func) : IO Unit :=
  match check f with
  | .ok _ => throw (IO.userError "accepted a representation-changing recursive cast")
  | .error _ => pure ()

def main : IO Unit := do
  -- Exact retained schema-11 list client; neither AIR nor historical Gen is rewritten.
  let raw ← get <| Raw.parseFile (← IO.FS.readFile "tests/golden/0.15.2/lists/air/lists.listSum.json")
  require (raw.body.any fun i => i.id == 66 && i.tag == "bitcast" &&
    i.ty == some 21 && i.args == #[.inst 65]) "retained raw list inst66 qualifier cast drift"
  require ((Raw.flatten raw.body).any fun i => i.id == 33 && i.tag == "bitcast" &&
    i.ty == some 5 && i.args == #[.inst 32]) "retained raw list inst33 optional wrap drift"
  let f : Func ← get <| normalize raw
  require (f.types[5]? == some (.optional 14)) "retained exact pointer wrapper shape drift"
  -- Isolate the wrapper from inst66 so failures cannot be masked by another cast.
  let insts := f.allInsts
  let some wrapInst := insts.find? (fun i => i.id == 25)
    | throw (IO.userError "retained canonical wrapper instruction missing")
  let .bitcast (.inst 18) := wrapInst.op
    | throw (IO.userError "retained canonical wrapper operand drift")
  require (wrapInst.ty == 5) "retained canonical wrapper result type drift"
  let wrapCx : CheckCtx := {
    fnName := f.name
    types := f.types
    layouts := f.layouts
    instTys := insts.map fun i => (i.id, i.ty)
    places := #[] }
  require (wrapCx.valTy? (.inst 18) == some 14) "retained canonical wrapper source type drift"
  discard (get <| checkOp wrapCx 4 wrapInst.ty wrapInst.op)
  IO.println "retained exact optional wrapper positive passed"
  let rejectWrap (cx : CheckCtx) : IO Unit := do
    match checkOp cx 4 wrapInst.ty wrapInst.op with
    | .ok _ => throw (IO.userError "accepted a representation-changing optional wrap")
    | .error _ => pure ()
  let wrapLayout := f.layouts[5]!
  rejectWrap {wrapCx with layouts := f.layouts.set! 5 {wrapLayout with ptrAlign := some 4}}
  rejectWrap {wrapCx with layouts := f.layouts.set! 5 {wrapLayout with sentinel := true}}
  rejectWrap {wrapCx with types := f.types.set! 5 (.optional 26)}
  rejectWrap {wrapCx with types := f.types.set! 14 (.ptr "many" false 25)}
  IO.println "retained four optional wrapper negatives passed"
  let sourceType : Option Ty := f.types[5]?
  let some (Ty.optional sourcePointer) := sourceType
    | throw (IO.userError "retained list source optional shape drift")
  let targetType : Option Ty := f.types[21]?
  let some (Ty.optional targetPointer) := targetType
    | throw (IO.userError "retained list target optional shape drift")
  require (f.types[sourcePointer]? == some (.ptr "one" false 25) &&
    f.types[targetPointer]? == some (.ptr "one" true 25)) "retained list qualifier type shape drift"
  discard (get <| check f)
  IO.println "retained full list checker passed"
  -- Full callee-closure generation/proofs are checked by ROOT affected gates;
  -- this exact retained client control checks every per-function instruction.
  -- The exception requires identical complete layouts, including pointer alignment.
  let original := f.layouts[targetPointer]!
  reject {f with layouts := f.layouts.set! targetPointer {original with ptrAlign := some 4}}
  reject {f with layouts := f.layouts.set! targetPointer {original with sentinel := true}}
  reject {f with layouts := f.layouts.set! targetPointer {original with hostSize := 8, bitOffset := 1}}
  -- Same child alone is insufficient: a one/many conversion is not const-only.
  reject {f with types := f.types.set! targetPointer (.ptr "many" true 25)}
  -- No blanket identical-child exception: unchanged constness still requires the scan.
  reject {f with types := f.types.set! targetPointer (.ptr "one" false 25)}
  IO.println "retained recursive list qualifier controls passed"
