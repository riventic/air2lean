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
  let .bitcast _ (.inst 18) := wrapInst.op
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
  let sourceType : Option Ty := f.types[5]?
  let some (Ty.optional sourcePointer) := sourceType
    | throw (IO.userError "retained list source optional shape drift")
  let targetType : Option Ty := f.types[21]?
  let some (Ty.optional targetPointer) := targetType
    | throw (IO.userError "retained list target optional shape drift")
  require (f.types[sourcePointer]? == some (.ptr "one" false 25) &&
    f.types[targetPointer]? == some (.ptr "one" true 25)) "retained list qualifier type shape drift"
  require (f.types[25]? == some (.struct "lists.Node" "auto" #[("val", 11), ("next", 5)]) &&
    f.types[11]? == some (.int false 32) && f.types[15]? == some (.errorSet (some #["OutOfMemory"])) &&
    f.types[19]? == some (.ptr "one" false 11)) "retained list node shape drift"
  discard (get <| check f)
  IO.println "retained full list checker passed"
  let some qualInst := insts.find? (fun i => i.ty == 21 && i.op matches .bitcast ..)
    | throw (IO.userError "retained canonical qualifier instruction missing")
  discard (get <| checkOp wrapCx 5 qualInst.ty qualInst.op)
  -- The capability walk follows cycles (`Check.lean`'s `errorCapabilityScan`, `cycles`): a cycle
  -- neither hides nor adds error storage. Every pointer-metadata mutation of the two retained
  -- casts gets the verdict it gets when `Node.next` is an acyclic error-free pointer (`*u32`):
  -- one rule for recursive and acyclic pointees, no recursion-only exception or rejection.
  let wrapLayout := f.layouts[5]!
  let original := f.layouts[targetPointer]!
  let wrapMutants : List CheckCtx := [
    {wrapCx with layouts := f.layouts.set! 5 {wrapLayout with ptrAlign := some 4}},
    {wrapCx with layouts := f.layouts.set! 5 {wrapLayout with sentinel := true}},
    {wrapCx with types := f.types.set! 5 (.optional 26)},
    {wrapCx with types := f.types.set! 14 (.ptr "many" false 25)}]
  let qualMutants : List CheckCtx := [
    {wrapCx with layouts := f.layouts.set! targetPointer {original with ptrAlign := some 4}},
    {wrapCx with layouts := f.layouts.set! targetPointer {original with sentinel := true}},
    {wrapCx with layouts := f.layouts.set! targetPointer {original with hostSize := 8, bitOffset := 1}},
    {wrapCx with types := f.types.set! targetPointer (.ptr "many" true 25)},
    {wrapCx with types := f.types.set! targetPointer (.ptr "one" false 25)}]
  let verdict (cx : CheckCtx) (i : Inst) : Bool := (checkOp cx 4 i.ty i.op).toBool
  let acyclic (cx : CheckCtx) : CheckCtx :=
    {cx with types := cx.types.set! 25 (.struct "lists.Node" "auto" #[("val", 11), ("next", 19)])}
  for (cx, i) in wrapMutants.map (·, wrapInst) ++ qualMutants.map (·, qualInst) do
    require (verdict cx i == verdict (acyclic cx) i) "a cycle changed a pointer-cast verdict"
  IO.println "retained recursive/acyclic verdict agreement passed (9 mutants)"
  -- Error storage reachable through the cycle: `Node.val` becomes the finite error set. Casts
  -- that keep the decoder pass; a cast whose recursive pointee has another error domain, also
  -- one reached only through `next`, exposes symbolic storage and is rejected.
  let n := f.types.size
  let errTypes := f.types.set! 25 (.struct "lists.Node" "auto" #[("val", 15), ("next", 5)]) ++ #[
    .errorSet (some #["Other"]),                                     -- n: another domain
    .struct "lists.Node" "auto" #[("val", n), ("next", n + 3)],      -- n+1: Node over `Other`
    .ptr "one" false (n + 1), .optional (n + 2),                     -- n+2, n+3
    .struct "lists.Node" "auto" #[("val", 15), ("next", n + 3)],     -- n+4: `Other` past `next`
    .ptr "one" false (n + 4), .optional (n + 5)]                     -- n+5, n+6
  let errLayouts := f.layouts ++ #[f.layouts[15]!, f.layouts[25]!, f.layouts[14]!, f.layouts[5]!,
    f.layouts[25]!, f.layouts[14]!, f.layouts[5]!]
  let errCx : CheckCtx := {wrapCx with types := errTypes, layouts := errLayouts}
  discard (get <| checkOp errCx 4 wrapInst.ty wrapInst.op)
  discard (get <| checkOp errCx 5 qualInst.ty qualInst.op)
  IO.println "error-bearing recursive wrap and qualifier positives passed"
  let rejectExposing (cx : CheckCtx) (ty : TyId) (op : Op) (message : String) : IO Unit :=
    match checkOp cx 4 ty op with
    | .ok _ => throw (IO.userError "accepted an error-domain-changing recursive pointer cast")
    | .error e => require ((e.splitOn message).length > 1) s!"wrong recursive cast rejection: {e}"
  let exposing := "a pointer cast exposing symbolic error storage"
  rejectExposing errCx (n + 3) wrapInst.op exposing
  rejectExposing errCx (n + 6) wrapInst.op exposing
  rejectExposing errCx 19 wrapInst.op exposing
  rejectExposing {errCx with types := errTypes.set! targetPointer (.ptr "one" true (n + 1))}
    qualInst.ty qualInst.op exposing
  rejectExposing {errCx with types := errTypes.set! targetPointer (.ptr "one" true (n + 4))}
    qualInst.ty qualInst.op exposing
  rejectExposing {errCx with instTys := #[(0, 7)]} 14 (.bitcast false (.inst 0))
    "recovering a symbolic error pointer"
  IO.println "error-bearing recursive cast negatives passed (6)"
  -- Exact observed 0.15 dupe shape: distinct e![]u8 IDs, identical finite domain/payload.
  let duplicateTypes : Array Ty := #[.int false 8, .errorSet (some #["OutOfMemory"]), .errorSet (some #["OutOfMemory"]), .ptr "slice" false 0, .errorUnion 1 3, .errorUnion 2 3]
  let duplicateLayouts : Array Layout := #[{size := some 1, align := some 1}, {size := some 2, align := some 2}, {size := some 2, align := some 2}, {size := some 16, align := some 8, ptrAlign := some 1}, {size := some 24, align := some 8}, {size := some 24, align := some 8}]
  let duplicateCx : CheckCtx := {fnName := "duplicateFiniteUnion", types := duplicateTypes, layouts := duplicateLayouts, instTys := #[(0,5)], places := #[]}
  require (duplicateCx.valTy? (.inst 0) == some 5) "duplicate finite union source binding drift"
  discard (get <| checkOp duplicateCx 0 4 (.bitcast false (.inst 0)))
  let rejectDuplicate (cx : CheckCtx) : IO Unit := do
    match checkOp cx 0 4 (.bitcast false (.inst 0)) with
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
