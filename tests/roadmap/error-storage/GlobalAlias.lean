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
  -- Exact input-validation regression: a self-referential pointer global is error-free.
  let recursiveTypes : Array Ty := #[.void, .ptr "one" false 1]
  let recursiveGlobal : Global := { name := some "recursive_plain", ty := 1, isConst := false, threadlocal := false, isExtern := false, init := some (.ptrConst 1 0 0) }
  let recursivePlain := { base "recursivePlainGlobal" recursiveGlobal with types := recursiveTypes, layouts := #[scalar 0 1, pointer 8], ret := 0, body := #[{id := 0, ty := 0, op := .ret .void}] }
  accept recursivePlain
  -- Direct global API isolates the alias decision before unrelated type-table checks.
  let recursiveCase (name : String) (extra : Array Ty) : Func :=
    { recursivePlain with name := "folded_alias." ++ name, types := #[.void, .ptr "one" false 2, .struct "RecursiveAlias" "auto" #[("next", 1), ("value", 3)]] ++ extra, layouts := #[scalar 0 1, pointer 8, {size := some 16, align := some 8, offsets := #[0,8]}] ++ (extra.map fun _ => scalar 2 2) }
  let recursiveError := recursiveCase "recursiveReachableError" #[.errorSet (some #["Alpha"])]
  let recursiveOpaque := recursiveCase "recursiveOpaque" #[.other "unresolved"]
  let recursiveInferred := recursiveCase "recursiveInferredError" #[.errorSet none]
  let recursiveUnknown := { recursiveCase "recursiveUnknown" #[.int false 16] with types := #[.void, .ptr "one" false 2, .struct "RecursiveAlias" "auto" #[("next", 1), ("missing", 99)], .int false 16] }
  let recursiveBudget := { recursiveCase "recursiveBudget" #[.int false 16] with types := #[.void, .ptr "one" false 2, .struct "RecursiveBudget" "auto" (#[("next", 1)] ++ ((Array.range 1024).map fun k => (s!"v{k}", 3))), .int false 16] }
  for control in #[recursiveError, recursiveOpaque, recursiveInferred, recursiveUnknown, recursiveBudget] do
    match checkGlobal control control.globals[0]! with
    | .ok _ => throw (IO.userError s!"accepted recursive alias negative {control.name}")
    | .error e => unless (e.splitOn "global alias has unresolved or cyclic symbolic storage provenance").length > 1 do
        throw (IO.userError s!"wrong recursive alias rejection {control.name}: {e}")
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
  let hostView := {loadAt "bitHostView" structGlobal 8 0 with layouts := layouts.set! 8 {size := some 8, align := some 8, ptrAlign := some 2, hostSize := 4, bitOffset := 16, vectorIndexExported := true}}
  reject hostView "overlaps symbolic error bytes"
  accept {loadAt "bitHostGuard" structGlobal 8 0 with layouts := layouts.set! 8 {size := some 8, align := some 8, ptrAlign := some 2, hostSize := 2, bitOffset := 0, vectorIndexExported := true}}
  let mixedItems := {base "mixedSymbolicItems" afterGlobal with ret := 0, body := #[ {id := 0, ty := 0, op := .ptrElemVal (.ptrConst 13 0 0) (.int 17 1)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  reject mixedItems "escaping, arithmetic"
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
  let ptrReturn (name : String) (g : Global) (pty off : Nat) : Func := {base name g with ret := pty, body := #[{id := 0, ty := 4, op := .ret (.ptrConst pty 0 off)}]}
  let constUnion := {unionGlobal with isConst := true}
  accept (ptrReturn "constSuccessfulPayload" constUnion 8 0)
  accept {base "constNumericPayloadProjection" constUnion with ret := 8, body := #[{id := 0, ty := 8, op := .errPayloadPtr false (.ptrConst 10 0 0)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  reject (loadAt "constSymbolicPayloadView" constUnion 7 0) "overlaps symbolic error bytes"
  -- Returning the symbolic pointer is rejected at inst0 before byte-overlap validation.
  reject (ptrReturn "constSymbolicPayloadEscape" constUnion 7 0) "inst 0: an escaping, arithmetic or unresolved pointer alias into an error-bearing global is outside the finite error-storage fragment"
  reject (ptrReturn "constSymbolicWholeEscape" constUnion 10 0) "escaping, arithmetic"
  accept {base "constTypedUnionLoad" constUnion with ret := 6, body := #[{id := 0, ty := 6, op := .load (.ptrConst 10 0 0)}, {id := 1, ty := 4, op := .ret (.inst 0)}]}
  reject {base "constMixedSymbolicMany" constUnion with ret := 0, body := #[{id := 0, ty := 0, op := .ptrElemVal (.ptrConst 13 0 0) (.int 17 1)}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "escaping, arithmetic"
  reject {base "ordinaryNumericSymbolicView" (global 1 (.int 1 53)) with ret := 0, body := #[{id := 0, ty := 0, op := .load (.ptrConst 7 0 0)}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "overlaps symbolic error bytes"
  reject {base "constNumericParentRecovery" constUnion with ret := 9, body := #[{id := 0, ty := 9, op := .fieldParentPtr (.ptrConst 8 0 0) 0}, {id := 1, ty := 4, op := .ret (.inst 0)}]} "recovering an error-bearing parent"
  let numericSlotPtr := types.size
  let symbolicSlotPtr := numericSlotPtr + 1
  let nestedTypes := types ++ #[.ptr "one" false 8, .ptr "one" true 7]
  let nestedLayouts := layouts ++ #[pointer 8, pointer 8]
  let nestedCase (name : String) (target : Nat) (address : Bool) : Func :=
    let middle : Array Inst := if address then #[{id := 3, ty := 17, op := .bitcast (.inst 1)}, {id := 4, ty := target, op := .bitcast (.inst 3)}] else #[{id := 4, ty := target, op := .bitcast (.inst 1)}]
    {base name constUnion with globals := #[], types := nestedTypes, layouts := nestedLayouts, params := #[8], ret := target, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := numericSlotPtr, op := .alloc}, {id := 2, ty := 3, op := .store (.inst 1) (.inst 0)}] ++ middle ++ #[{id := 5, ty := 4, op := .ret (.inst 4)}]}
  reject (nestedCase "calleeNestedPointerRecovery" symbolicSlotPtr false) "a pointer cast exposing symbolic error storage"
  reject (nestedCase "calleeNestedAddressRecovery" symbolicSlotPtr true) "recovering a symbolic error pointer"
  reject {base "calleeSymbolicSlotBytes" constUnion with globals := #[], types := nestedTypes, layouts := nestedLayouts, params := #[symbolicSlotPtr], ret := 0, body := #[{id := 0, ty := symbolicSlotPtr, op := .arg 0}, {id := 1, ty := 7, op := .bitcast (.inst 0)}, {id := 2, ty := 0, op := .load (.inst 1)}, {id := 3, ty := 4, op := .ret (.inst 2)}]} "a pointer cast exposing symbolic error storage"
  let maskedA := types.size + 2
  let maskedB := maskedA + 1
  let maskedAPtr := maskedA + 2
  let maskedBPtr := maskedA + 3
  let maskedTypes := nestedTypes ++ #[.struct "MaskedNumericCapability" "auto" #[("tag", 0), ("p", 8)], .struct "MaskedSymbolicCapability" "auto" #[("tag", 0), ("p", 7)], .ptr "one" false maskedA, .ptr "one" true maskedB]
  let maskedLayouts := nestedLayouts ++ #[{size := some 16, align := some 8, offsets := #[0,8]}, {size := some 16, align := some 8, offsets := #[0,8]}, pointer 8, pointer 8]
  reject {base "calleeMaskedPointerRecovery" constUnion with globals := #[], types := maskedTypes, layouts := maskedLayouts, params := #[8], ret := maskedBPtr, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := maskedAPtr, op := .alloc}, {id := 2, ty := 7, op := .fieldPtr (.inst 1) 0}, {id := 3, ty := 3, op := .store (.inst 2) (.err 0 "Alpha")}, {id := 4, ty := numericSlotPtr, op := .fieldPtr (.inst 1) 1}, {id := 5, ty := 3, op := .store (.inst 4) (.inst 0)}, {id := 6, ty := maskedBPtr, op := .bitcast (.inst 1)}, {id := 7, ty := 4, op := .ret (.inst 6)}]} "a pointer cast exposing symbolic error storage"
  accept (nestedCase "calleeNumericDoublePointer" numericSlotPtr false)
  accept (nestedCase "calleeNumericDoubleAddress" numericSlotPtr true)
  let cycleTy := types.size
  let cyclePtr := cycleTy + 1
  let cycleTypes := types ++ #[.struct "CapabilityCycle" "auto" #[("next", cyclePtr)], .ptr "one" false cycleTy]
  let cycleLayouts := layouts ++ #[{size := some 8, align := some 8, offsets := #[0]}, pointer 8]
  -- G2 (docs/c-frontend.md): an error-free self-referential graph has capability `false` (a
  -- least fixpoint), so a cast into it is an ordinary numeric view.
  accept {base "cyclicCapabilityCast" constUnion with globals := #[], types := cycleTypes, layouts := cycleLayouts, params := #[8], ret := cyclePtr, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := cyclePtr, op := .bitcast (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]}
  -- A cycle that reaches an error keeps the strict acyclic walk: rejected as before (L10).
  let errCycleTypes := types ++ #[.struct "ErrorCycle" "auto" #[("next", cyclePtr), ("code", 0)], .ptr "one" false cycleTy]
  let errCycleLayouts := layouts ++ #[{size := some 16, align := some 8, offsets := #[0, 8]}, pointer 8]
  reject {base "cyclicErrorCapabilityCast" constUnion with globals := #[], types := errCycleTypes, layouts := errCycleLayouts, params := #[8], ret := cyclePtr, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := cyclePtr, op := .bitcast (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]} "unresolved or cyclic symbolic storage provenance"
  reject {base "cyclicErrorIdentityCast" constUnion with globals := #[], types := errCycleTypes, layouts := errCycleLayouts, params := #[cyclePtr], ret := cyclePtr, body := #[{id := 0, ty := cyclePtr, op := .arg 0}, {id := 1, ty := cyclePtr, op := .bitcast (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]} "unresolved or cyclic symbolic storage provenance"
  -- `*anyopaque` is an error-free opaque view: numeric storage round-trips through it, error
  -- storage cannot enter or leave it, and neither can storage the model keeps symbolically
  -- (`std.mem.Allocator`, `std.Thread`, `std.Io`).
  let opaqueTy := types.size
  let opaquePtr := opaqueTy + 1
  let allocTy := opaqueTy + 2
  let allocPtr := opaqueTy + 3
  let opaqueTypes := types ++ #[.other "anyopaque", .ptr "one" false opaqueTy, .allocator, .ptr "one" false allocTy]
  let opaqueLayouts := layouts ++ #[{}, pointer 1, scalar 16 8, pointer 8]
  let castChain (name : String) (src dst : TyId) (via : Option TyId := some opaquePtr) : Func :=
    let insts := match via with
      | some v => #[{id := 0, ty := src, op := .arg 0}, {id := 1, ty := v, op := .bitcast (.inst 0)}, {id := 2, ty := dst, op := .bitcast (.inst 1)}, {id := 3, ty := 4, op := .ret (.inst 2)}]
      | none => #[{id := 0, ty := src, op := .arg 0}, {id := 2, ty := dst, op := .bitcast (.inst 0)}, {id := 3, ty := 4, op := .ret (.inst 2)}]
    {base name constUnion with globals := #[], types := opaqueTypes, layouts := opaqueLayouts, params := #[src], ret := dst, body := insts}
  accept (castChain "opaqueNumericRoundTrip" 8 8)
  accept (castChain "numericToOpaque" 8 opaquePtr none)
  reject (castChain "opaqueFromError" 7 7) "a pointer cast exposing symbolic error storage"
  reject (castChain "opaqueToError" opaquePtr 7 none) "a pointer cast exposing symbolic error storage"
  reject (castChain "opaqueFromAllocator" allocPtr 8) "symbolic model encoding"
  reject (castChain "opaqueToAllocator" opaquePtr allocPtr none) "symbolic model encoding"
  reject (castChain "numericToAllocator" 8 allocPtr none) "symbolic model encoding"
  accept (castChain "allocatorIdentity" allocPtr allocPtr none)
  -- Any other opaque type stays outside the subset.
  reject {castChain "namedOpaqueView" 8 opaquePtr none with types := opaqueTypes.set! opaqueTy (.other "opaque")} "outside the subset"
  let capBudgetTypes := types ++ #[.struct "CapabilityBudget" "auto" ((Array.range 1024).map fun k => (s!"n{k}", 1)), .ptr "one" false cycleTy]
  let capBudgetLayouts := layouts ++ #[{size := some 2048, align := some 2, offsets := (Array.range 1024).map (· * 2)}, pointer 2]
  reject {base "exhaustedCapabilityCast" constUnion with globals := #[], types := capBudgetTypes, layouts := capBudgetLayouts, params := #[8], ret := cyclePtr, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := cyclePtr, op := .bitcast (.inst 0)}, {id := 2, ty := 4, op := .ret (.inst 1)}]} "unresolved or cyclic symbolic storage provenance"
  reject {base "calleeNumericAddressRecovery" constUnion with globals := #[], params := #[8], ret := 0, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := 17, op := .bitcast (.inst 0)}, {id := 2, ty := 7, op := .bitcast (.inst 1)}, {id := 3, ty := 0, op := .load (.inst 2)}, {id := 4, ty := 4, op := .ret (.inst 3)}]} "recovering a symbolic error pointer"
  reject {base "calleeNumericPointerRecovery" constUnion with globals := #[], params := #[8], ret := 0, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := 7, op := .bitcast (.inst 0)}, {id := 2, ty := 0, op := .load (.inst 1)}, {id := 3, ty := 4, op := .ret (.inst 2)}]} "a pointer cast exposing symbolic error storage"
  reject {base "calleeNumericParentRecovery" constUnion with globals := #[], params := #[8], ret := 9, body := #[{id := 0, ty := 8, op := .arg 0}, {id := 1, ty := 9, op := .fieldParentPtr (.inst 0) 0}, {id := 2, ty := 4, op := .ret (.inst 1)}]} "recovering an error-bearing parent"
  reject (ptrReturn "mutableSuccessfulPayload" unionGlobal 8 0) "escaping, arithmetic"
  reject (ptrReturn "constTypedError" {errorGlobal with isConst := true} 7 0) "escaping, arithmetic"
  reject (loadAt "constRawError" {errorGlobal with isConst := true} 8 0) "overlaps symbolic error bytes"
  reject (ptrReturn "constErrorArm" {constUnion with init := some (.errUnionErr 6 "Alpha")} 8 0) "escaping, arithmetic"
  reject (loadAt "constRawErrorArm" {constUnion with init := some (.errUnionErr 6 "Alpha")} 8 2) "overlaps symbolic error bytes"
  reject (ptrReturn "constUndefined" {constUnion with init := some (.undef 6)} 8 0) "escaping, arithmetic"
  -- A partly undefined initial value is rejected before alias analysis (L12).
  reject (ptrReturn "constUndefinedPayload" {constUnion with init := some (.errUnionOk 6 (.undef 1))} 8 0) "a partly `undefined` initial value is outside the subset"
  reject (ptrReturn "constUnknownInit" {constUnion with init := none} 8 0) "no initial value"
  reject (ptrReturn "constExtern" {constUnion with isExtern := true} 8 0) "`extern`"
  reject (ptrReturn "constThreadlocal" {constUnion with threadlocal := true} 8 0) "`threadlocal`"
  let pointerHolderTy := types.size
  let pointerHolderPtr := pointerHolderTy + 1
  let pointerHolderTypes := types.push (.struct "ImmutablePointerHolder" "auto" #[("p", 8), ("status", 6)]) |>.push (.ptr "one" true pointerHolderTy)
  let pointerHolderLayouts := layouts.push {size := some 16, align := some 8, offsets := #[0,8]} |>.push (pointer 8)
  let pointerHolder := {global pointerHolderTy (.agg pointerHolderTy #[.ptrConst 8 1 0, .errUnionOk 6 (.int 1 53)]) with isConst := true}
  reject {ptrReturn "constPointerField" pointerHolder pointerHolderPtr 0 with types := pointerHolderTypes, layouts := pointerHolderLayouts, globals := #[pointerHolder, global 1 (.int 1 11)]} "escaping, arithmetic"
  let budgetArray := types.size
  let budgetPtr := budgetArray + 1
  let budgetCase (count : Nat) : Func :=
    let ts := types.push (.array count 6 false) |>.push (.ptr "one" true budgetArray)
    let ls := layouts.push (scalar (count * 4) 2) |>.push (pointer 2)
    let g := {global budgetArray (.agg budgetArray (Array.replicate count (.errUnionOk 6 (.int 1 53)))) with isConst := true}
    {ptrReturn "constCertificateBudget" g 8 0 with types := ts, layouts := ls}
  accept (budgetCase 509)
  reject (budgetCase 510) "escaping, arithmetic"
  -- Exact L06 frozen constructor tree: Failure!u8/u64/u16 successes plus ?Payload.
  -- Offsets are explicit modeled layouts, not a new native/compiler attestation.
  let u32 := types.size
  let failure := u32 + 1
  let payloadTy := u32 + 2
  let optionalTy := u32 + 3
  let smallTy := u32 + 4
  let wideTy := u32 + 5
  let equalTy := u32 + 6
  let innerTy := u32 + 7
  let outerTy := u32 + 8
  let bytePtr := u32 + 9
  let halfPtr := u32 + 10
  let widePtr := u32 + 11
  let manyBytePtr := u32 + 12
  let byteSlice := u32 + 13
  let l06Types := types ++ #[.int false 32, .errorSet (some #["Bad"]), .struct "L06.Payload" "auto" #[("guard", u32), ("value", 2)], .optional payloadTy, .errorUnion failure 2, .errorUnion failure 17, .errorUnion failure 1, .struct "L06.Inner" "auto" #[("optional", optionalTy), ("small", smallTy), ("wide", wideTy), ("equal", equalTy)], .struct "L06.Outer" "auto" #[("before", 17), ("inner", innerTy), ("after", 17)], .ptr "one" true 2, .ptr "one" true 1, .ptr "one" true 17, .ptr "many" true 2, .ptr "slice" true 2]
  let l06Layouts := layouts ++ #[scalar 4 4, scalar 2 2, {size := some 8, align := some 4, offsets := #[0,4]}, scalar 12 4, scalar 4 2, scalar 16 8, scalar 4 2, {size := some 40, align := some 8, offsets := #[16,28,0,32]}, {size := some 56, align := some 8, offsets := #[0,8,48]}, pointer 1, pointer 2, pointer 8, pointer 1, scalar 16 8]
  let innerValue : Val := .agg innerTy #[.optSome optionalTy (.agg payloadTy #[.int u32 0xabcdef01, .int 2 7]), .errUnionOk smallTy (.int 2 19), .errUnionOk wideTy (.int 17 41), .errUnionOk equalTy (.int 1 23)]
  let frozen := {global outerTy (.agg outerTy #[.int 17 0x0102030405060708, innerValue, .int 17 0x1112131415161718]) with name := some "storage.frozen", isConst := true}
  let getter (name : String) (pty off : Nat) : Func := {ptrReturn name frozen pty off with types := l06Types, layouts := l06Layouts}
  accept (getter "L06.optionalPtr" bytePtr 28)
  accept (getter "L06.smallPtr" bytePtr 38)
  accept (getter "L06.widePtr" widePtr 8)
  accept (getter "L06.equalPtr" halfPtr 40)
  accept (getter "L06.sameOptionalPtr" bytePtr 28)
  accept {getter "L06.optionalSlice" byteSlice 28 with body := #[{id := 0, ty := 4, op := .ret (.sliceConst byteSlice (.ptrConst manyBytePtr 0 28) (.int 17 1))}]}
  let badInner : Val := .agg innerTy #[.optSome optionalTy (.agg payloadTy #[.int u32 0xabcdef01, .int 2 7]), .errUnionErr smallTy "Bad", .errUnionOk wideTy (.int 17 41), .errUnionOk equalTy (.int 1 23)]
  let badFrozen := {frozen with init := some (.agg outerTy #[.int 17 0x0102030405060708, badInner, .int 17 0x1112131415161718])}
  reject {getter "L06.constErrorArmElsewhere" bytePtr 28 with globals := #[badFrozen]} "escaping, arithmetic"
  reject {getter "L06.mutableBacking" bytePtr 28 with globals := #[{frozen with isConst := false}]} "escaping, arithmetic"
  reject {getter "L06.incompleteConstructor" bytePtr 28 with globals := #[{frozen with init := some (.agg outerTy #[innerValue])}]} "escaping, arithmetic"
  -- Byte-payload offset 2 and nested single-branch blocks match writeSmall's actual AIR shape.
  let smallTy := types.size
  let smallPtr := smallTy + 1
  let branchTypes := types ++ #[.errorUnion 0 2, .ptr "one" false smallTy]
  let branchLayouts := layouts ++ #[scalar 4 2, pointer 2]
  let smallGlobal := global smallTy (.errUnionOk smallTy (.int 2 19))
  let branchBase := {base "singleBranchPayloadStore" smallGlobal with types := branchTypes, layouts := branchLayouts, ret := 2}
  let nestedPayload : Array Inst := #[{id := 2, ty := 21, op := .errPayloadPtr false (.ptrConst smallPtr 0 0)}, {id := 3, ty := 4, op := .br 1 (.inst 2)}]
  let outerPayload : Array Inst := #[{id := 1, ty := 21, op := .block nestedPayload}, {id := 4, ty := 4, op := .br 0 (.inst 1)}]
  let storeTail : Array Inst := #[{id := 5, ty := 3, op := .store (.inst 0) (.int 2 31)}, {id := 6, ty := 2, op := .load (.inst 0)}, {id := 7, ty := 4, op := .ret (.inst 6)}]
  accept {branchBase with body := #[{id := 0, ty := 21, op := .block outerPayload}] ++ storeTail}
  let joined := nestedPayload.push {id := 8, ty := 4, op := .br 1 (.inst 2)}
  reject {branchBase with name := "folded_alias.multiBranchPayload", body := #[{id := 0, ty := 21, op := .block (#[{id := 1, ty := 21, op := .block joined}, {id := 4, ty := 4, op := .br 0 (.inst 1)}])}] ++ storeTail} "escaping, arithmetic"
  reject {branchBase with name := "folded_alias.singleBranchOverlap", body := #[{id := 0, ty := 21, op := .block #[{id := 2, ty := 21, op := .bitcast (.ptrConst smallPtr 0 0)}, {id := 3, ty := 4, op := .br 0 (.inst 2)}]}] ++ storeTail} "overlaps symbolic error bytes"
  reject {branchBase with name := "folded_alias.singleBranchEscape", ret := 21, body := #[{id := 0, ty := 21, op := .block outerPayload}, {id := 5, ty := 4, op := .ret (.inst 0)}]} "escaping, arithmetic"
  reject {branchBase with name := "folded_alias.singleBranchUnknownArithmetic", params := #[17], body := #[{id := 9, ty := 17, op := .arg 0}, {id := 0, ty := 21, op := .block #[{id := 2, ty := 21, op := .ptrAdd false (.ptrConst 21 0 2) (.inst 9)}, {id := 3, ty := 4, op := .br 0 (.inst 2)}]}] ++ storeTail} "escaping, arithmetic"
  let shadowed : Array Inst := #[{id := 0, ty := 21, op := .block outerPayload}, {id := 0, ty := 21, op := .block #[]}]
  reject {branchBase with name := "folded_alias.singleBranchDuplicateBlockId", body := shadowed ++ storeTail} "escaping, arithmetic"
  -- A transparent branch chain still cannot exceed the fixed-origin recursion budget.
  let mut deep : Inst := {id := 257, ty := 21, op := .errPayloadPtr false (.ptrConst smallPtr 0 0)}
  for k in (List.range 257).reverse do
    let child := deep
    deep := {id := k, ty := 21, op := .block #[child, {id := 1000 + k, ty := 4, op := .br k (.inst child.id)}]}
  reject {branchBase with name := "folded_alias.singleBranchBudget", body := #[deep, {id := 2001, ty := 3, op := .store (.inst 0) (.int 2 31)}, {id := 2002, ty := 2, op := .load (.inst 0)}, {id := 2003, ty := 4, op := .ret (.inst 2002)}]} "escaping, arithmetic"
  -- Code identity is not arbitrary opaque memory: exact named immutable function only.
  let codeTy := types.size
  let codePtr := codeTy + 1
  let otherCode := codeTy + 2
  let wrongCodePtr := codeTy + 3
  let opaqueTy := codeTy + 4
  let opaquePtr := codeTy + 5
  let codeTypes := types ++ #[.other "fn (u16) u16", .ptr "one" true codeTy,
    .other "fn (u8) u8", .ptr "one" true otherCode, .other "opaque", .ptr "one" true opaqueTy]
  let codeLayouts := layouts ++ #[{}, pointer 1, {}, pointer 1, {}, pointer 1]
  let codeGlobal : Global := { name := some "folded_alias.codeTarget", ty := codeTy, isConst := true, threadlocal := false, isExtern := false, init := some (.func "folded_alias.codeTarget" false none) }
  let codeAddress : Func := { base "codeAddress" codeGlobal with types := codeTypes, layouts := codeLayouts, ret := codePtr, body := #[{id := 0, ty := 4, op := .ret (.ptrConst codePtr 0 0)}] }
  let codeTarget : Func := { base "codeTarget" codeGlobal with types := codeTypes, layouts := codeLayouts, globals := #[], params := #[1], ret := 1, body := #[{id := 0, ty := 1, op := .arg 0}, {id := 1, ty := 4, op := .ret (.inst 0)}] }
  match check codeAddress >>= fun _ => checkProgram #[codeAddress, codeTarget] with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"rejected exact named code address: {e}")
  reject { codeAddress with name := "folded_alias.codeOffset", body := #[{id := 0, ty := 4, op := .ret (.ptrConst codePtr 0 1)}] }
    "unresolved or cyclic symbolic storage provenance"
  reject { codeAddress with name := "folded_alias.codeReinterpret", ret := wrongCodePtr, body := #[{id := 0, ty := 4, op := .ret (.ptrConst wrongCodePtr 0 0)}] }
    "unresolved or cyclic symbolic storage provenance"
  reject { codeAddress with name := "folded_alias.opaqueBacking", ret := opaquePtr, globals := #[{ codeGlobal with ty := opaqueTy, init := some (.undef opaqueTy) }], body := #[{id := 0, ty := 4, op := .ret (.ptrConst opaquePtr 0 0)}] }
    "type 'opaque' is outside the subset"
  -- An error-code bit-pointer is rejected by the packed-field check (L08) before provenance.
  reject { codeAddress with name := "folded_alias.codeBitPointer", layouts := codeLayouts.set! codePtr { pointer 1 with hostSize := 1, vectorIndexExported := true } }
    "a bit-pointer to a type other than an integer, a `bool`, an enum or a packed struct"
  reject { codeAddress with name := "folded_alias.codeWrongGlobal", body := #[{id := 0, ty := 4, op := .ret (.ptrConst codePtr 99 0)}] }
    "unknown global id 99"
  reject { codeAddress with name := "folded_alias.codeWrongName", globals := #[{codeGlobal with name := some "folded_alias.otherTarget"}] }
    "unresolved or cyclic symbolic storage provenance"
  for (label, restricted) in #[("sentinel", { pointer 1 with sentinel := true }), ("volatile", { pointer 1 with isVolatile := true }), ("allowzero", { pointer 1 with allowzero := true })] do
    reject { codeAddress with name := "folded_alias.codeFlag." ++ label, layouts := codeLayouts.set! codePtr restricted }
      "unresolved or cyclic symbolic storage provenance"
  IO.println "finite global alias controls passed"
