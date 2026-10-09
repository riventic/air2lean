import Air2Lean
import Air2Lean.Check
open Air2Lean

private def get (out : Except String α) : IO α := match out with
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)

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
  -- The wrapper exception matters where the general rules reject: an error-free recursive
  -- `lists.Node` has capability `false` (G2, a least fixpoint), so the negatives give `Node`
  -- an error field. A cyclic error-bearing graph keeps the strict acyclic walk (L10).
  let errNode := f.types.set! 25 (.struct "lists.Node" "auto" #[("val", 17), ("next", 5)])
  let errCx := {wrapCx with types := errNode}
  discard (get <| checkOp errCx 4 wrapInst.ty wrapInst.op)
  let wrapLayout := f.layouts[5]!
  rejectWrap {errCx with layouts := f.layouts.set! 5 {wrapLayout with ptrAlign := some 4}}
  rejectWrap {errCx with layouts := f.layouts.set! 5 {wrapLayout with sentinel := true}}
  rejectWrap {errCx with types := errNode.set! 5 (.optional 26)}
  rejectWrap {errCx with types := errNode.set! 14 (.ptr "many" false 25)}
  -- G2: the same const/many conversions of the error-free recursive graph are accepted.
  discard (get <| checkOp {wrapCx with types := f.types.set! 5 (.optional 26)} 4 wrapInst.ty wrapInst.op)
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
  -- Checked on the qualifier cast alone (raw inst66), with the error-bearing `Node` above (see the wrapper controls).
  let some qualInst := insts.find? (fun i => i.ty == 21 && i.op matches .bitcast _)
    | throw (IO.userError "retained qualifier instruction missing")
  let qualCx : CheckCtx := {errCx with instTys := insts.map fun i => (i.id, i.ty)}
  discard (get <| checkOp qualCx 4 qualInst.ty qualInst.op)
  let rejectQual (cx : CheckCtx) : IO Unit := do
    match checkOp cx 4 qualInst.ty qualInst.op with
    | .ok _ => throw (IO.userError "accepted a representation-changing recursive cast")
    | .error _ => pure ()
  let original := f.layouts[targetPointer]!
  rejectQual {qualCx with layouts := f.layouts.set! targetPointer {original with ptrAlign := some 4}}
  rejectQual {qualCx with layouts := f.layouts.set! targetPointer {original with sentinel := true}}
  rejectQual {qualCx with layouts := f.layouts.set! targetPointer {original with hostSize := 8, bitOffset := 1}}
  -- Same child alone is insufficient: a one/many conversion is not const-only.
  rejectQual {qualCx with types := errNode.set! targetPointer (.ptr "many" true 25)}
  -- No blanket identical-child exception: unchanged constness still requires the scan.
  rejectQual {qualCx with types := errNode.set! targetPointer (.ptr "one" false 25)}
  -- G2: the error-free recursive list graph needs no exception.
  discard (get <| check {f with types := f.types.set! targetPointer (.ptr "one" false 25)})
  IO.println "retained recursive list qualifier controls passed"
  -- Exact observed 0.15 dupe shape: distinct e![]u8 IDs, identical finite domain/payload.
  let duplicateTypes : Array Ty := #[.int false 8, .errorSet (some #["OutOfMemory"]), .errorSet (some #["OutOfMemory"]), .ptr "slice" false 0, .errorUnion 1 3, .errorUnion 2 3]
  let duplicateLayouts : Array Layout := #[{size := some 1, align := some 1}, {size := some 2, align := some 2}, {size := some 2, align := some 2}, {size := some 16, align := some 8, ptrAlign := some 1}, {size := some 24, align := some 8}, {size := some 24, align := some 8}]
  let duplicateCx : CheckCtx := {fnName := "duplicateFiniteUnion", types := duplicateTypes, layouts := duplicateLayouts, instTys := #[(0,5)], places := #[]}
  require (duplicateCx.valTy? (.inst 0) == some 5) "duplicate finite union source binding drift"
  discard (get <| checkOp duplicateCx 0 4 (.bitcast (.inst 0)))
  let rejectDuplicate (cx : CheckCtx) : IO Unit := do
    match checkOp cx 0 4 (.bitcast (.inst 0)) with
    | .ok _ => throw (IO.userError "accepted a representation-changing finite union cast")
    | .error e => require ((e.splitOn "opaque bitcast involving optional, aggregate or error-union error storage").length > 1) s!"wrong finite union rejection: {e}"
  rejectDuplicate {duplicateCx with types := duplicateTypes.set! 2 (.errorSet (some #["Other"]))}
  rejectDuplicate {duplicateCx with types := duplicateTypes.set! 2 (.errorSet (some #["OutOfMemory", "Extra"]))}
  rejectDuplicate {duplicateCx with types := duplicateTypes.set! 4 (.errorUnion 1 0)}
  rejectDuplicate {duplicateCx with layouts := duplicateLayouts.set! 4 {size := some 32, align := some 8}}
  rejectDuplicate {duplicateCx with layouts := duplicateLayouts.set! 1 {size := some 4, align := some 2}}
  rejectDuplicate {duplicateCx with layouts := duplicateLayouts.set! 4 {size := none, align := some 8}}
  rejectDuplicate {duplicateCx with types := duplicateTypes.set! 2 (.errorSet none)}
  rejectDuplicate {duplicateCx with types := duplicateTypes.set! 1 (.errorSet (some #["OutOfMemory", "OutOfMemory"])) |>.set! 2 (.errorSet (some #["OutOfMemory", "OutOfMemory"]))}
  rejectDuplicate {duplicateCx with types := duplicateTypes.set! 4 (.errorUnion 1 99) |>.set! 5 (.errorUnion 2 99)}
  rejectDuplicate {duplicateCx with layouts := duplicateLayouts.set! 3 {size := none, align := some 8}}
  IO.println "finite duplicate error-union controls passed"
