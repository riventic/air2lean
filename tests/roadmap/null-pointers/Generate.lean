import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Offline AIR/schema/checker/emitter regressions. Generates standalone semantic test files;
compilers are invoked only by the serialized external check driver. -/
open Lean Air2Lean
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) := obj [("inst", num n)]
private def lit (t : Nat) (v : String) := obj [("ty", num t), ("val", .str v)]
private def intTy (bits : Nat) := obj [("k", .str "int"), ("signed", .bool false),
  ("bits", num bits), ("abi_size", num (Zig.intSize bits)), ("abi_align", num (Zig.intAlign bits))]
private def ptrTy (size : String) (child : Nat) (allowzero : Bool := false) (align : Nat := 1) :=
  obj [("k", .str "ptr"), ("size", .str size), ("child", num child), ("const", .bool false),
    ("allowzero", .bool allowzero), ("ptr_align", num align), ("abi_size", num 8), ("abi_align", num 8)]
private def boolTy := obj [("k", .str "bool")]
private def nrTy := obj [("k", .str "noreturn")]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def file (name : String) (types : Array Json) (params : Array Nat) (ret : Nat)
    (body : Array Json) := obj [("schema", num 11), ("zig_version", .str "0.16.0"),
  ("name", .str name), ("types", .arr types), ("params", toJson params),
  ("ret", num ret), ("body", .arr body)]
private def nullVal (ty : Nat) (off : Nat := 0) := obj [("ty", num ty),
  ("ptr", obj [("null", .bool true), ("off", num off)])]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def accept (j : Json) : IO Func := do
  match process j with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def reject (j : Json) (diagnostic : String) : IO Unit := do
  match process j with
  | .ok _ => throw (IO.userError s!"accepted rejection fixture: {diagnostic}")
  | .error e => unless (e.splitOn diagnostic).length > 1 do
      throw (IO.userError s!"wrong rejection: expected {diagnostic}, got {e}")
private def writeCase (dir : System.FilePath) (name : String) (j : Json) (tests : String)
    (needles : List String := []) : IO Unit := do
  let f ← accept j
  let source := emit #[f] "Nullable" ""
  for needle in needles do
    unless (source.splitOn needle).length > 1 do
      throw (IO.userError s!"{name}: emitted translation lacks {needle}")
  IO.FS.writeFile (dir / (name ++ ".lean")) (source ++
    "\nprivate def value (f : Zig.MemM α) : Option α := ((f.run {}).run.bind Except.toOption).map Prod.fst\n" ++
    "private def failure (f : Zig.MemM α) (e : Zig.Error) : Bool := match (f.run {}).run with | some (.error got) => decide (got = e) | _ => false\n" ++ tests ++ "\n")
private def types (size : String := "c") (allowzero : Bool := false) :=
  #[intTy 64, intTy 8, ptrTy size 1 allowzero, boolTy, nrTy, ptrTy "one" 1]
/-- Storage, aggregate and projection types after `types`: 6 `*[*c]u8` (8-aligned),
7 `extern struct Node { next: [*c]u8, val: u8 }`, 8 `[*c]Node`, 9 `[*c][*c]u8`,
10 `[2][*c]u8`, 11 `*[2][*c]u8`, 12 `?*u8`, 13 `*Node`. -/
private def storageTypes (size : String := "c") (allowzero : Bool := false) :=
  (types size allowzero) ++ #[ptrTy "one" 2 (align := 8),
    obj [("k", .str "struct"), ("name", .str "Node"), ("layout", .str "extern"),
      ("abi_size", num 16), ("abi_align", num 8),
      ("fields", .arr #[obj [("name", .str "next"), ("ty", num 2), ("offset", num 0)],
        obj [("name", .str "val"), ("ty", num 1), ("offset", num 8)]])],
    ptrTy "c" 7 (align := 8), ptrTy "c" 2 (align := 8),
    obj [("k", .str "array"), ("len", num 2), ("child", num 2), ("abi_size", num 16), ("abi_align", num 8)],
    ptrTy "one" 10 (align := 8),
    obj [("k", .str "optional"), ("child", num 5), ("abi_size", num 8), ("abi_align", num 8)],
    ptrTy "one" 7 (align := 8)]
private def argInsts (tys : List Nat) : Array Json :=
  (tys.toArray.mapIdx fun i t => inst i "arg" t #[] [("param", num i)])
/-- Shared runtime helpers for the storage cases: a live 8-aligned heap block and raw bytes. -/
private def storageHelpers : String := "
private def zeros (n : Nat) : Zig.Mem := { blocks := #[{ bytes := Array.replicate n (.int 0), align := 8, kind := .heap, live := true, addr := 4096 }], nextAddr := 4096 + n + 1 }
private def block0 : Zig.Ptr := ⟨some 0, 0⟩
private def valueIn (m : Zig.Mem) (f : Zig.MemM α) : Option α := ((f.run m).run.bind Except.toOption).map Prod.fst
private def failureIn (m : Zig.Mem) (f : Zig.MemM α) (e : Zig.Error) : Bool := match (f.run m).run with | some (.error got) => decide (got = e) | _ => false
private def bytesAfter (m : Zig.Mem) (f : Zig.MemM α) : Option (Array Zig.Byte) := match (f.run m).run with | some (.ok (_, m')) => m'.blocks[0]?.map (·.bytes) | _ => none
"
private def castInput (name tag : String) := file name (types) #[0] 3
  #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "bitcast" 2 #[ref 0],
    inst 2 tag 3 #[ref 1], inst 3 "ret" 4 #[ref 2]]
private def pointerInput (name tag : String) (ret : Nat) := file name (types) #[2] ret
  #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 tag ret #[ref 0], inst 2 "ret" 4 #[ref 1]]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Generate.lean OUTPUT_DIR")
  let dir := System.FilePath.mk directory
  IO.FS.createDirAll dir
  writeCase dir "cNull" (castInput "cNull" "is_null")
    "example : value (Nullable.cNull 0) = some true := by native_decide\nexample : value (Nullable.cNull 1) = some false := by native_decide\nexample : value (Nullable.cNull 18446744073709551615) = some false := by native_decide"
  writeCase dir "cNonNull" (castInput "cNonNull" "is_non_null")
    "example : value (Nullable.cNonNull 0) = some false := by native_decide\nexample : value (Nullable.cNonNull 8) = some true := by native_decide"
  writeCase dir "allowzeroAddress" (file "allowzeroAddress" (types "one" true) #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "bitcast" 2 #[ref 0],
      inst 2 "bitcast" 0 #[ref 1], inst 3 "ret" 4 #[ref 2]])
    "example : (value (Nullable.allowzeroAddress 0)).map BitVec.toNat = some 0 := by native_decide\nexample : (value (Nullable.allowzeroAddress 18446744073709551615)).map BitVec.toNat = some 18446744073709551615 := by native_decide"
  writeCase dir "allowzeroManyAddress" (file "allowzeroManyAddress" (types "many" true) #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "bitcast" 2 #[ref 0],
      inst 2 "bitcast" 0 #[ref 1], inst 3 "ret" 4 #[ref 2]])
    "example : (value (Nullable.allowzeroManyAddress 0)).map BitVec.toNat = some 0 := by native_decide\nexample : (value (Nullable.allowzeroManyAddress 65535)).map BitVec.toNat = some 65535 := by native_decide"
  writeCase dir "cZero" (file "cZero" (types) #[] 2 #[inst 0 "ret" 4 #[nullVal 2]])
    "example : value Nullable.cZero = some Zig.Ptr.null := by native_decide"
  writeCase dir "cCast" (pointerInput "cCast" "bitcast" 5)
    "example : failure (Nullable.cCast Zig.Ptr.null) .panic = true := by native_decide\nexample : value (Nullable.cCast ⟨none, 123⟩) = some ⟨none, 123⟩ := by native_decide"
  writeCase dir "cUnwrap" (pointerInput "cUnwrap" "optional_payload" 2)
    "example : failure (Nullable.cUnwrap Zig.Ptr.null) .panic = true := by native_decide\nexample : value (Nullable.cUnwrap ⟨none, 7⟩) = some ⟨none, 7⟩ := by native_decide"
  writeCase dir "cLoad" (pointerInput "cLoad" "load" 1)
    "example : failure (Nullable.cLoad Zig.Ptr.null) .illegal = true := by native_decide\nexample : failure (Nullable.cLoad ⟨none, 123⟩) .illegal = true := by native_decide\nprivate def liveRead : Zig.MemM (BitVec 8) := do\n  let p ← Zig.alloc .heap 1 1\n  Zig.store 1 p (42#8)\n  Nullable.cLoad p\nexample : value liveRead = some 42#8 := by native_decide\nprivate def deadRead : Zig.MemM (BitVec 8) := do\n  let p ← Zig.alloc .heap 1 1\n  Zig.free p\n  Nullable.cLoad p\nexample : failure deadRead .illegal = true := by native_decide"
  writeCase dir "cEqual" (file "cEqual" (types) #[2, 2] 3
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "arg" 2 #[] [("param", num 1)],
      inst 2 "cmp_eq" 3 #[ref 0, ref 1], inst 3 "ret" 4 #[ref 2]])
    "example : value (Nullable.cEqual Zig.Ptr.null Zig.Ptr.null) = some true := by native_decide\nexample : value (Nullable.cEqual Zig.Ptr.null ⟨none, 1⟩) = some false := by native_decide\nprivate def sameAddressMemory : Zig.Mem := { blocks := #[{ bytes := Array.replicate 32 .undef, align := 1, kind := .heap, live := true, addr := 100 }] }\nexample : (((Nullable.cEqual ⟨some 0, 20⟩ ⟨none, 120⟩).run sameAddressMemory).run.bind Except.toOption).map Prod.fst = some true := by native_decide"
  -- Nullable storage: a stored C pointer, including address zero, is eight zero bytes.
  writeCase dir "storeLoad" (file "storeLoad" (storageTypes) #[6, 2] 2
    (argInsts [6, 2] ++ #[inst 2 "store" 4 #[ref 0, ref 1], inst 3 "load" 2 #[ref 0], inst 4 "ret" 4 #[ref 3]]))
    (storageHelpers ++ "example : valueIn (zeros 8) (Nullable.storeLoad block0 Zig.Ptr.null) = some Zig.Ptr.null := by native_decide
example : bytesAfter (zeros 8) (Nullable.storeLoad block0 Zig.Ptr.null) = some (Array.replicate 8 (.int 0)) := by native_decide
example : valueIn (zeros 16) (Nullable.storeLoad block0 ⟨some 0, 8⟩) = some ⟨some 0, 8⟩ := by native_decide
example : valueIn (zeros 8) (Nullable.storeLoad block0 ⟨none, 77⟩) = some ⟨none, 77⟩ := by native_decide
example : failureIn (zeros 8) (Nullable.storeLoad Zig.Ptr.null Zig.Ptr.null) .illegal = true := by native_decide
example : failureIn (zeros 4) (Nullable.storeLoad block0 Zig.Ptr.null) .illegal = true := by native_decide")
    ["Zig.nullablePtrEnc"]
  writeCase dir "storedIsNull" (file "storedIsNull" (storageTypes) #[6] 3
    (argInsts [6] ++ #[inst 1 "load" 2 #[ref 0], inst 2 "is_null" 3 #[ref 1], inst 3 "ret" 4 #[ref 2]]))
    (storageHelpers ++ "example : valueIn (zeros 8) (Nullable.storedIsNull block0) = some true := by native_decide
private def undefMem : Zig.Mem := { blocks := #[{ bytes := Array.replicate 8 .undef, align := 8, kind := .heap, live := true, addr := 4096 }], nextAddr := 4105 }
example : failureIn undefMem (Nullable.storedIsNull block0) .unspecified = true := by native_decide
private def storedLive : Zig.MemM Bool := do
  let p ← Zig.alloc .heap 8 8
  let q ← Zig.alloc .heap 1 1
  letI : Zig.Enc Zig.Ptr := Zig.nullablePtrEnc
  Zig.store 8 p q
  Nullable.storedIsNull p
example : valueIn {} storedLive = some false := by native_decide")
    ["Zig.nullablePtrEnc"]
  let allowzeroStorage := storageTypes "one" true
  writeCase dir "allowzeroStoreLoad" (file "allowzeroStoreLoad" allowzeroStorage #[6, 2] 2
    (argInsts [6, 2] ++ #[inst 2 "store" 4 #[ref 0, ref 1], inst 3 "load" 2 #[ref 0], inst 4 "ret" 4 #[ref 3]]))
    (storageHelpers ++ "example : bytesAfter (zeros 8) (Nullable.allowzeroStoreLoad block0 Zig.Ptr.null) = some (Array.replicate 8 (.int 0)) := by native_decide
example : valueIn (zeros 8) (Nullable.allowzeroStoreLoad block0 Zig.Ptr.null) = some Zig.Ptr.null := by native_decide")
    ["Zig.nullablePtrEnc"]
  -- Aggregates: a C pointer field in an extern struct, in memory and as a value.
  writeCase dir "nodeNext" (file "nodeNext" (storageTypes) #[8] 2
    (argInsts [8] ++ #[inst 1 "struct_field_ptr" 9 #[ref 0] [("index", num 0)],
      inst 2 "load" 2 #[ref 1], inst 3 "ret" 4 #[ref 2]]))
    -- The offset-0 field pointer of address zero is defined; the load through it is not.
    (storageHelpers ++ "example : failureIn (zeros 16) (Nullable.nodeNext Zig.Ptr.null) .illegal = true := by native_decide
example : failureIn (zeros 16) (Nullable.nodeNext ⟨none, 4096⟩) .illegal = true := by native_decide
example : valueIn (zeros 16) (Nullable.nodeNext block0) = some Zig.Ptr.null := by native_decide")
    -- Field 0: a constant offset 0 is the base itself (no `getelementptr`, no projection).
    ["let i1 ← pure p0"]
  -- The same field with a nonnullable result type (0.14.1/0.15.2 typing): address zero must not
  -- become a `*[*c]u8`, so even offset 0 is checked (`ptrProjectNonnull`), not `pure p0`.
  writeCase dir "nodeNextNonnull" (file "nodeNextNonnull" (storageTypes) #[8] 2
    (argInsts [8] ++ #[inst 1 "struct_field_ptr" 6 #[ref 0] [("index", num 0)],
      inst 2 "load" 2 #[ref 1], inst 3 "ret" 4 #[ref 2]]))
    (storageHelpers ++ "example : failureIn (zeros 16) (Nullable.nodeNextNonnull Zig.Ptr.null) .illegal = true := by native_decide
example : valueIn (zeros 16) (Nullable.nodeNextNonnull block0) = some Zig.Ptr.null := by native_decide")
    ["Zig.ptrProjectNonnull p0 (·.add 0)"]
  writeCase dir "nodeVal" (file "nodeVal" (storageTypes) #[8] 1
    (argInsts [8] ++ #[inst 1 "struct_field_ptr" 2 #[ref 0] [("index", num 1)],
      inst 2 "load" 1 #[ref 1], inst 3 "ret" 4 #[ref 2]]))
    (storageHelpers ++ "example : failureIn (zeros 16) (Nullable.nodeVal Zig.Ptr.null) .illegal = true := by native_decide
example : valueIn (zeros 16) (Nullable.nodeVal block0) = some 0#8 := by native_decide")
    ["Zig.ptrProject"]
  writeCase dir "nodeRoundTrip" (file "nodeRoundTrip" (storageTypes) #[13, 1] 7
    (argInsts [13, 1] ++ #[inst 2 "aggregate_init" 7 #[nullVal 2, ref 1],
      inst 3 "store" 4 #[ref 0, ref 2], inst 4 "load" 7 #[ref 0],
      inst 5 "struct_field_val" 2 #[ref 4] [("index", num 0)],
      inst 6 "is_null" 3 #[ref 5], inst 7 "cond_br" 4 #[ref 6]
        [("then", .arr #[inst 8 "ret" 4 #[ref 4]]), ("else", .arr #[inst 9 "trap" 4])]]))
    (storageHelpers ++ "example : (valueIn (zeros 16) (Nullable.nodeRoundTrip block0 9)).map (·.val) = some 9#8 := by native_decide
example : (valueIn (zeros 16) (Nullable.nodeRoundTrip block0 9)).map (·.next) = some Zig.Ptr.null := by native_decide
example : (bytesAfter (zeros 16) (Nullable.nodeRoundTrip block0 9)).map (·.extract 0 8) = some (Array.replicate 8 (.int 0)) := by native_decide")
    ["Zig.nullablePtrEnc"]
  writeCase dir "arrayItem" (file "arrayItem" (storageTypes) #[11, 0] 2
    (argInsts [11, 0] ++ #[inst 2 "ptr_elem_val" 2 #[ref 0, ref 1], inst 3 "ret" 4 #[ref 2]]))
    (storageHelpers ++ "example : valueIn (zeros 16) (Nullable.arrayItem block0 1) = some Zig.Ptr.null := by native_decide
example : failureIn (zeros 16) (Nullable.arrayItem block0 2) .illegal = true := by native_decide")
    ["Zig.nullablePtrEnc"]
  -- Projections from a C pointer are pointer formation (`Zig.ptrProject`, MM-3): offset 0 is
  -- the base; any other offset needs a block that holds base and result (LLVM's
  -- `getelementptr inbounds`), so none from address zero or a provenance-free address.
  writeCase dir "cAdd" (file "cAdd" (types) #[2, 0] 2
    (argInsts [2, 0] ++ #[inst 2 "ptr_add" 2 #[ref 0, ref 1], inst 3 "ret" 4 #[ref 2]]))
    "example : failure (Nullable.cAdd Zig.Ptr.null 1) .illegal = true := by native_decide
example : value (Nullable.cAdd Zig.Ptr.null 0) = some Zig.Ptr.null := by native_decide
example : failure (Nullable.cAdd ⟨none, 100⟩ 2) .illegal = true := by native_decide
private def liveAdd : Zig.MemM Zig.Ptr := do
  let p ← Zig.alloc .heap 2 1
  Nullable.cAdd p 2
example : value liveAdd = some ⟨some 0, 2⟩ := by native_decide
private def pastAdd : Zig.MemM Zig.Ptr := do
  let p ← Zig.alloc .heap 2 1
  Nullable.cAdd p 3
example : failure pastAdd .illegal = true := by native_decide"
    ["Zig.ptrProject"]
  -- `&p[i]` keeps the projection; a load through it (`p[i]`) is `cElem`'s item access.
  writeCase dir "cIndex" (file "cIndex" (types) #[2, 0] 5
    (argInsts [2, 0] ++ #[inst 2 "ptr_elem_ptr" 5 #[ref 0, ref 1], inst 3 "ret" 4 #[ref 2]]))
    "example : failure (Nullable.cIndex Zig.Ptr.null 0) .illegal = true := by native_decide
example : failure (Nullable.cIndex ⟨none, 4096⟩ 3) .illegal = true := by native_decide
example : failure (do Zig.load (BitVec 8) 1 (← Nullable.cIndex ⟨none, 4096⟩ 0)) .illegal = true := by native_decide
private def liveIndex : Zig.MemM (BitVec 8) := do
  let p ← Zig.alloc .heap 2 1
  Zig.store 1 (p.add 1) (42#8)
  Zig.load (BitVec 8) 1 (← Nullable.cIndex p 1)
example : value liveIndex = some 42#8 := by native_decide
private def pastEnd : Zig.MemM (BitVec 8) := do
  let p ← Zig.alloc .heap 2 1
  Zig.load (BitVec 8) 1 (← Nullable.cIndex p 2)
example : failure pastEnd .illegal = true := by native_decide"
    ["Zig.ptrProjectNonnull"]
  writeCase dir "cElem" (file "cElem" (types) #[2, 0] 1
    (argInsts [2, 0] ++ #[inst 2 "ptr_elem_val" 1 #[ref 0, ref 1], inst 3 "ret" 4 #[ref 2]]))
    "example : failure (Nullable.cElem Zig.Ptr.null 0) .illegal = true := by native_decide
private def liveElem : Zig.MemM (BitVec 8) := do
  let p ← Zig.alloc .heap 2 1
  Zig.store 1 (p.add 1) (7#8)
  Nullable.cElem p 1
example : value liveElem = some 7#8 := by native_decide"
  -- Permitted casts between C pointers and ordinary optional pointers.
  writeCase dir "toOptional" (file "toOptional" (storageTypes) #[2] 12
    (argInsts [2] ++ #[inst 1 "bitcast" 12 #[ref 0], inst 2 "ret" 4 #[ref 1]]))
    "example : value (Nullable.toOptional Zig.Ptr.null) = some none := by native_decide
example : value (Nullable.toOptional ⟨none, 5⟩) = some (some ⟨none, 5⟩) := by native_decide"
    ["Zig.ptrToOptional"]
  writeCase dir "fromOptional" (file "fromOptional" (storageTypes) #[12] 2
    (argInsts [12] ++ #[inst 1 "bitcast" 2 #[ref 0], inst 2 "ret" 4 #[ref 1]]))
    "example : value (Nullable.fromOptional none) = some Zig.Ptr.null := by native_decide
example : value (Nullable.fromOptional (some ⟨none, 5⟩)) = some ⟨none, 5⟩ := by native_decide"
    ["Zig.ptrOfOptional"]
  reject (file "badZero" (types "one") #[] 2 #[inst 0 "ret" 4 #[nullVal 2]]) "address-zero constant requires"
  reject (file "badOffset" (types) #[] 2 #[inst 0 "ret" 4 #[nullVal 2 1]]) "nonzero offset"
  let ambiguous := obj [("ty", num 2), ("ptr", obj [("null", .bool true), ("off", num 0), ("unsupported", .str "int")])]
  reject (file "ambiguous" (types) #[] 2 #[inst 0 "ret" 4 #[ambiguous]]) "ambiguous null pointer"
  let fixed := obj [("ty", num 2), ("ptr", obj [("unsupported", .str "int"), ("off", num 1)])]
  reject (file "fixed" (types) #[] 2 #[inst 0 "ret" 4 #[fixed]]) "pointer constant without a global"
  -- A successful type check on the first operand must not skip the second
  -- operand's null or unsupported-pointer validation for that same type ID.
  reject (file "repeatedNullableType" (types) #[] 3
    #[inst 0 "cmp_eq" 3 #[nullVal 2, fixed], inst 1 "ret" 4 #[ref 0]])
    "pointer constant without a global"
  let ordinary := obj [("ty", num 2), ("ptr", obj [("global", num 0), ("off", num 0)])]
  let repeatedOrdinary := (file "repeatedOrdinaryType" (types "one") #[] 3
    #[inst 0 "cmp_eq" 3 #[ordinary, nullVal 2], inst 1 "ret" 4 #[ref 0]]).setObjVal!
    "globals" (.arr #[obj [("ty", num 1), ("const", .bool true), ("init", lit 1 "0")]])
  reject repeatedOrdinary "address-zero constant requires"
  for (size, zero) in #[ ("c", false), ("one", true) ] do
    let ts := (types size zero).push (obj [("k", .str "optional"), ("child", num 2)])
    reject (file "optionalNullable" ts #[6] 6
      #[inst 0 "arg" 6 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "separate null flag"
    -- A stored optional of a nullable pointer stays out: it needs a separate null flag.
    let ts := (types size zero) ++ #[obj [("k", .str "optional"), ("child", num 2)], ptrTy "one" 6]
    reject (file "storedOptionalNullable" ts #[7] 6
      #[inst 0 "arg" 7 #[] [("param", num 0)], inst 1 "load" 6 #[ref 0], inst 2 "ret" 4 #[ref 1]]) "separate null flag"
  let ts := (types).push (ptrTy "slice" 1)
  reject (file "nullableSlice" ts #[2, 0] 6
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "arg" 0 #[] [("param", num 1)],
      inst 2 "slice" 6 #[ref 0, ref 1], inst 3 "ret" 4 #[ref 2]]) "nonnull cast first"
  reject (file "nullableMemset" (types) #[2, 0] 0
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "arg" 0 #[] [("param", num 1)],
      inst 2 "memset" 4 #[ref 0, lit 1 "0"], inst 3 "ret" 4 #[ref 1]]) "nonnull cast first"
  let ts := (types) ++ #[ptrTy "slice" 1, obj [("k", .str "optional"), ("child", num 6)]]
  reject (file "optionalSliceCast" ts #[2] 7
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "bitcast" 7 #[ref 0], inst 2 "ret" 4 #[ref 1]]) "optional slice"
  let ts := (types).push (obj [("k", .str "optional"), ("child", num 5)])
  reject (file "wrapNullable" ts #[2] 6
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "wrap_optional" 6 #[ref 0], inst 2 "ret" 4 #[ref 1]]) "explicit null wrapping"
  let ts := (types).push (obj [("k", .str "union"), ("name", .str "Box"), ("layout", .str "extern"),
    ("fields", .arr #[obj [("name", .str "pointer"), ("ty", num 2)]])])
  reject (file "unionNullable" ts #[6] 6
    #[inst 0 "arg" 6 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "nullable pointers in aggregate values"
  let ts := (types).push (obj [("k", .str "tuple"), ("fields", .arr #[obj [("ty", num 2)], obj [("ty", num 1)]])])
  reject (file "tupleNullable" ts #[6] 6
    #[inst 0 "arg" 6 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "nullable pointers in aggregate values"
  let ts := (types) ++ #[obj [("k", .str "error_set"), ("errors", .arr #[.str "Bad"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 2)]]
  reject (file "errorUnionNullable" ts #[7] 7
    #[inst 0 "arg" 7 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "error-union payloads"
  let ts := #[intTy 64, intTy 8, (ptrTy "c" 1).setObjVal! "volatile" (.bool true), boolTy, nrTy]
  reject (file "volatileNullable" ts #[2] 2
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "volatile nullable pointers"
  IO.println "nullable pointer source pipeline: 22 generated cases; adjacent rejections checked"
