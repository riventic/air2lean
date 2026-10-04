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
private def ptrTy (size : String) (child : Nat) (allowzero : Bool := false) :=
  obj [("k", .str "ptr"), ("size", .str size), ("child", num child), ("const", .bool false),
    ("allowzero", .bool allowzero), ("ptr_align", num 1), ("abi_size", num 8), ("abi_align", num 8)]
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
private def writeCase (dir : System.FilePath) (name : String) (j : Json) (tests : String) : IO Unit := do
  let f ← accept j
  IO.FS.writeFile (dir / (name ++ ".lean")) (emit #[f] "Nullable" "" ++
    "\nprivate def value (f : Zig.MemM α) : Option α := ((f.run {}).run.bind Except.toOption).map Prod.fst\n" ++
    "private def failure (f : Zig.MemM α) (e : Zig.Error) : Bool := match (f.run {}).run with | some (.error got) => decide (got = e) | _ => false\n" ++ tests ++ "\n")
private def types (size : String := "c") (allowzero : Bool := false) :=
  #[intTy 64, intTy 8, ptrTy size 1 allowzero, boolTy, nrTy, ptrTy "one" 1]
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
  reject (file "badZero" (types "one") #[] 2 #[inst 0 "ret" 4 #[nullVal 2]]) "address-zero constant requires"
  reject (file "badOffset" (types) #[] 2 #[inst 0 "ret" 4 #[nullVal 2 1]]) "nonzero offset"
  let ambiguous := obj [("ty", num 2), ("ptr", obj [("null", .bool true), ("off", num 0), ("unsupported", .str "int")])]
  reject (file "ambiguous" (types) #[] 2 #[inst 0 "ret" 4 #[ambiguous]]) "ambiguous null pointer"
  let fixed := obj [("ty", num 2), ("ptr", obj [("unsupported", .str "int"), ("off", num 1)])]
  reject (file "fixed" (types) #[] 2 #[inst 0 "ret" 4 #[fixed]]) "pointer constant without a global"
  for (size, zero) in #[ ("c", false), ("one", true) ] do
    let ts := (types size zero).push (obj [("k", .str "optional"), ("child", num 2)])
    reject (file "optionalNullable" ts #[6] 6
      #[inst 0 "arg" 6 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "separate null flag"
    let ts := (types size zero).push (ptrTy "one" 2)
    reject (file "storedNullable" ts #[6] 2
      #[inst 0 "arg" 6 #[] [("param", num 0)], inst 1 "load" 2 #[ref 0], inst 2 "ret" 4 #[ref 1]]) "null-byte encoding"
  reject (file "nullableArithmetic" (types) #[2] 2
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "ptr_add" 2 #[ref 0, lit 0 "1"], inst 2 "ret" 4 #[ref 1]]) "nonnull cast first"
  let ts := (types).push (obj [("k", .str "optional"), ("child", num 5)])
  reject (file "optionalCast" ts #[2] 6
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "bitcast" 6 #[ref 0], inst 2 "ret" 4 #[ref 1]]) "explicit null wrapping"
  reject (file "wrapNullable" ts #[2] 6
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "wrap_optional" 6 #[ref 0], inst 2 "ret" 4 #[ref 1]]) "explicit null wrapping"
  let ts := (types).push (obj [("k", .str "struct"), ("name", .str "Box"), ("layout", .str "auto"),
    ("fields", .arr #[obj [("name", .str "pointer"), ("ty", num 2)]])])
  reject (file "aggregateNullable" ts #[6] 6
    #[inst 0 "arg" 6 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "nullable pointers in aggregate values"
  let ts := #[intTy 64, intTy 8, (ptrTy "c" 1).setObjVal! "volatile" (.bool true), boolTy, nrTy]
  reject (file "volatileNullable" ts #[2] 2
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "ret" 4 #[ref 0]]) "volatile nullable pointers"
  IO.println "nullable pointer source pipeline: 9 generated cases; adjacent rejections checked"
