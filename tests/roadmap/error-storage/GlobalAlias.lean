import Air2Lean.Check
open Air2Lean

private def types : Array Ty := #[
  .errorSet (some #["Alpha", "Beta", "Gamma"]), .int false 16, .int false 8, .void, .noreturn,
  .struct "AliasS" "auto" #[("guard", 1), ("code", 0)], .errorUnion 0 1,
  .ptr "one" false 0, .ptr "one" false 1, .ptr "one" false 5, .ptr "one" false 6,
  .ptr "many" false 1, .ptr "c" false 1, .ptr "many" false 0, .optional 8,
  .struct "AliasHolder" "auto" #[("p", 8)], .ptr "one" false 15, .int false 64,
  .array 2 0 false, .ptr "one" false 18, .ptr "slice" false 0, .ptr "one" false 2,
  .struct "AliasAfter" "auto" #[("code", 0), ("guard", 1)]]
private def scalar (s a : Nat) : Layout := {size := some s, align := some a}
private def pointer (a : Nat) : Layout := {size := some 8, align := some 8, ptrAlign := some a}
private def layouts : Array Layout := #[
  scalar 2 2, scalar 2 2, scalar 1 1, scalar 0 1, {},
  {size := some 4, align := some 2, offsets := #[0,2]}, scalar 4 2,
  pointer 2, pointer 2, pointer 2, pointer 2, pointer 2, pointer 2, pointer 2, scalar 8 8,
  {size := some 8, align := some 8, offsets := #[0]}, pointer 8, scalar 8 8,
  scalar 4 2, pointer 2, scalar 16 8, pointer 1,
  {size := some 4, align := some 2, offsets := #[0,2]}]
private def global (ty : TyId) (value : Val) : Global :=
  {name := some "folded_alias.backing", ty, isConst := false, threadlocal := false, isExtern := false, init := some value}
private def errorGlobal := global 0 (.err 0 "Beta")
private def structGlobal := global 5 (.agg 5 #[.int 1 37, .err 0 "Gamma"])
private def unionGlobal := global 6 (.errUnionOk 6 (.int 1 53))
private def base (name : String) (g : Global) : Func :=
  {zigVersion := "0.16.0", name := "folded_alias." ++ name, params := #[], ret := 1, types, layouts, globals := #[g], body := #[]}
private def loadAt (name : String) (g : Global) (pty off : Nat) : Func :=
  {base name g with body := #[{id := 0, ty := 1, op := .load (.ptrConst pty 0 off)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
private def accept (f : Func) : IO Unit := do
  match check f >>= fun _ => checkProgram #[f] with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"rejected control {f.name}: {e}")
private def reject (f : Func) (message : String) : IO Unit := do
  match check f >>= fun _ => checkProgram #[f] with
  | .ok _ => throw (IO.userError s!"accepted negative {f.name}")
  | .error e => unless (e.splitOn message).length > 1 do
      throw (IO.userError s!"wrong rejection for {f.name}: {e}")

def main : IO Unit := do
  reject (loadAt "rawStandalone" errorGlobal 8 0) "overlaps symbolic error bytes"
  reject (loadAt "rawField" structGlobal 8 2) "overlaps symbolic error bytes"
  reject ({loadAt "partialByte" errorGlobal 21 1 with ret := 2, body := #[{id := 0, ty := 2, op := .load (.ptrConst 21 0 1)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}) "overlaps symbolic error bytes"
  accept (loadAt "legalGuard" structGlobal 8 0)
  accept (loadAt "legalFixedPayload" unionGlobal 8 0)
  let payload := {base "legalPayloadProjection" unionGlobal with body := #[ {id := 0, ty := 8, op := .errPayloadPtr false (.ptrConst 10 0 0)}, {id := 1, ty := 1, op := .load (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]}
  accept payload
  let exact := {base "typedError" errorGlobal with ret := 0, body := #[ {id := 0, ty := 0, op := .load (.ptrConst 7 0 0)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  accept exact
  accept {base "typedField" structGlobal with ret := 0, body := #[ {id := 0, ty := 0, op := .load (.ptrConst 7 0 2)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  reject {base "typedErrorReturn" errorGlobal with ret := 7, body := #[{id := 0, ty := 4, op := .ret (.ptrConst 7 0 0)}]} "escaping, arithmetic"
  let arrayGlobal := global 18 (.agg 18 #[.err 0 "Alpha", .err 0 "Beta"])
  accept {base "typedErrorArray" arrayGlobal with ret := 0, body := #[ {id := 0, ty := 0, op := .load (.ptrConst 13 0 2)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  let nested := {base "nestedConstant" errorGlobal with ret := 15, body := #[{id := 0, ty := 4, op := .ret (.agg 15 #[.ptrConst 8 0 0])}]}
  reject nested "outside the finite error-storage fragment"
  reject (loadAt "rawMany" structGlobal 11 0) "many/C/slice alias"
  reject (loadAt "rawC" structGlobal 12 0) "many/C/slice alias"
  let converted := {base "convertedMany" structGlobal with body := #[ {id := 0, ty := 11, op := .bitcast (.ptrConst 8 0 0)}, {id := 1, ty := 11, op := .ptrAdd false (.inst 0) (.int 17 1)}, {id := 2, ty := 1, op := .load (.inst 1)}, {id := 3, ty := 4, op := .ret (.inst 2)}]}
  reject converted "many/C/slice alias"
  let advanced := {base "advancedOne" structGlobal with body := #[ {id := 0, ty := 8, op := .ptrAdd false (.ptrConst 8 0 0) (.int 17 1)}, {id := 1, ty := 1, op := .load (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]}
  reject advanced "overlaps symbolic error bytes"
  let dynamic := {base "dynamicAdvance" structGlobal with params := #[17], body := #[ {id := 0, ty := 17, op := .arg 0}, {id := 1, ty := 8, op := .ptrAdd false (.ptrConst 8 0 0) (.inst 0)}, {id := 2, ty := 1, op := .load (.inst 1)}, {id := 3, ty := 4, op := .ret (.inst 2)}]}
  reject dynamic "unresolved pointer alias"
  let afterGlobal := global 22 (.agg 22 #[.err 0 "Alpha", .int 1 67])
  accept (loadAt "legalAfterGuard" afterGlobal 8 2)
  reject (loadAt "backwardMany" afterGlobal 11 2) "many/C/slice alias"
  reject {base "escapeReturn" structGlobal with ret := 8, body := #[{id := 0, ty := 4, op := .ret (.ptrConst 8 0 0)}]} "escaping, arithmetic"
  reject {base "escapeCall" structGlobal with body := #[ {id := 0, ty := 1, op := .call (.func "unresolved" false none) #[.ptrConst 8 0 0]}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "escaping, arithmetic"
  reject {base "addressLaunder" structGlobal with ret := 17, body := #[ {id := 0, ty := 17, op := .bitcast (.ptrConst 8 0 0)}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "escaping, arithmetic"
  let holderGlobal := global 15 (.agg 15 #[.ptrConst 8 0 0])
  reject {base "nestedInitializer" errorGlobal with globals := #[errorGlobal, holderGlobal], body := #[ {id := 0, ty := 4, op := .ret (.int 1 0)}]} "outside the finite error-storage fragment"
  reject {loadAt "missingOffsets" structGlobal 8 0 with layouts := layouts.set! 5 (scalar 4 2)} "no field offsets"
  let big := types.size
  let bigTypes := types.push (.struct "AliasBudget" "auto" ((Array.range 1024).map fun k => (s!"e{k}", 0)))
  let bigLayouts := layouts.push {size := some 2048, align := some 2, offsets := (Array.range 1024).map (· * 2)}
  let bigGlobal := global big (.agg big (Array.replicate 1024 (.err 0 "Alpha")))
  reject {exact with name := "folded_alias.budget", types := bigTypes, layouts := bigLayouts, globals := #[bigGlobal], body := #[{id := 0, ty := 0, op := .load (.ptrConst 7 0 2046)}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "unresolved subobject/layout"
  let hostView := {loadAt "bitHostView" structGlobal 8 0 with layouts := layouts.set! 8 {size := some 8, align := some 8, ptrAlign := some 2, hostSize := 4, bitOffset := 16}}
  reject hostView "overlaps symbolic error bytes"
  accept {loadAt "bitHostGuard" structGlobal 8 0 with layouts := layouts.set! 8 {size := some 8, align := some 8, ptrAlign := some 2, hostSize := 2, bitOffset := 0}}
  let mixedItems := {base "mixedSymbolicItems" afterGlobal with ret := 0, body := #[ {id := 0, ty := 0, op := .ptrElemVal (.ptrConst 13 0 0) (.int 17 1)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  reject mixedItems "many/C/slice alias"
  reject {base "aggregateCall" structGlobal with body := #[ {id := 0, ty := 1, op := .call (.func "unresolved" false none) #[.ptrConst 9 0 0]}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "escaping, arithmetic"
  let typedSlice := {base "localTypedSlice" arrayGlobal with ret := 0, body := #[ {id := 0, ty := 20, op := .slice (.ptrConst 13 0 0) (.int 17 2)}, {id := 1, ty := 0, op := .sliceElemVal (.inst 0) (.int 17 1)}, {id := 2, ty := 4, op := .ret (.inst 1)}]}
  accept typedSlice
  let nameTy := types.size
  let nameTypes := types.push (.ptr "slice" true 2)
  let nameLayouts := layouts.push (scalar 16 8)
  accept {base "errorName" errorGlobal with types := nameTypes, layouts := nameLayouts, ret := nameTy, body := #[{id := 0, ty := 0, op := .load (.ptrConst 7 0 0)}, {id := 1, ty := nameTy, op := .errorName (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]}
  let numericArrayTy := types.size
  let numericArrayPtr := numericArrayTy + 1
  let ordinaryTypes := types.push (.array 2 1 false) |>.push (.ptr "one" false numericArrayTy)
  let ordinaryLayouts := layouts.push (scalar 4 2) |>.push (pointer 2)
  let numericGlobal := {global numericArrayTy (.agg numericArrayTy #[.int 1 11, .int 1 13]) with name := some "folded_alias.numeric"}
  let indexGlobal := global 5 (.agg 5 #[.int 1 0, .err 0 "Gamma"])
  accept {base "ordinaryIndexedByGuard" indexGlobal with types := ordinaryTypes, layouts := ordinaryLayouts, globals := #[indexGlobal, numericGlobal], body := #[ {id := 0, ty := 1, op := .load (.ptrConst 8 0 0)}, {id := 1, ty := 8, op := .elemPtr (.ptrConst numericArrayPtr 1 0) (.inst 0)}, {id := 2, ty := 1, op := .load (.inst 1)}, {id := 3, ty := 4, op := .ret (.inst 2)}]}
  IO.println "finite global alias controls passed"
