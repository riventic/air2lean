import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Hand-written AIR (exporter schema 11) for roadmap L11's callable-address table.
The driver checks and emits the fixtures, and writes elaborated behavior assertions. -/
open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def lit (n : Nat) : Json := obj [("ty", num 0), ("val", .str (toString n))]
private def usize (n : Nat) : Json := obj [("ty", num 8), ("val", .str (toString n))]
private def gptr (ty global : Nat) (off : Nat := 0) : Json :=
  obj [("ty", num ty), ("ptr", obj [("global", num global), ("off", num off)])]
private def intTy (bits : Nat) : Json :=
  obj [("k", .str "int"), ("signed", .bool false), ("bits", num bits),
    ("abi_size", num (bits / 8)), ("abi_align", num (bits / 8))]
private def ptr (child : Nat) (isConst : Bool := true) (align : Option Nat := none) : Json :=
  obj <| (align.map fun a => [("ptr_align", num a)]).getD [] ++ [("k", .str "ptr"), ("size", .str "one"), ("const", .bool isConst), ("child", num child),
    ("volatile", .bool false), ("allowzero", .bool false), ("sentinel", .bool false),
    ("host_size", num 0), ("abi_size", num 8), ("abi_align", num 8)]
private def fnTy (name : String) : Json := obj [("k", .str "other"), ("name", .str name)]

/-- One type table for every fixture. `2` is `*const fn (u32) u32`; `7` points to a
function of a different signature; `13` is a data pointer. -/
private def types : Array Json := #[
  intTy 32, fnTy "fn (u32) u32", ptr 1,
  obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)], obj [("k", .str "noreturn")],
  obj [("k", .str "bool"), ("abi_size", num 1), ("abi_align", num 1)],
  fnTy "fn (u32, u32) u32", ptr 6, intTy 64,
  obj [("k", .str "array"), ("len", num 3), ("child", num 2), ("sentinel", .bool false),
    ("abi_size", num 24), ("abi_align", num 8)],
  obj [("k", .str "struct"), ("name", .str "Ops"), ("layout", .str "auto"),
    ("abi_size", num 16), ("abi_align", num 8),
    ("fields", .arr #[obj [("name", .str "f"), ("ty", num 2), ("offset", num 0)],
      obj [("name", .str "k"), ("ty", num 0), ("offset", num 8)]])],
  ptr 10 true (some 8), ptr 2 false (some 8), ptr 0 true (some 4),
  fnTy "fn (*const fn (u32) u32, u32) u32", ptr 2 true (some 8), ptr 10 false (some 8),
  fnTy "fn (*const Ops, u32) u32", fnTy "fn (**const fn (u32) u32, u32) u32"]

private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def arg (id param ty : Nat) : Json := inst id "arg" ty #[] [("param", num param)]
private def call (id : Nat) (callee : Json) (args : Array Json) (ty : Nat := 0) : Json :=
  inst id "call" ty args [("callee", callee)]
private def ret (id : Nat) (v : Json) : Json := inst id "ret" 4 #[v]
private def br (id target : Nat) : Json :=
  inst id "br" 4 #[obj [("ty", num 3), ("val", .str "{}")]] [("target", num target)]

/-- A named function block: the exporter's global for an address-taken function. -/
private def fnGlobal (name : String) (ty : Nat := 1) : Json :=
  obj [("name", .str name), ("ty", num ty), ("const", .bool true), ("threadlocal", .bool false),
    ("extern", .bool false), ("init", obj [("ty", num ty), ("func", .str name), ("noreturn", .bool false)])]
private def dataGlobal (name : String) (isConst : Bool) (ty : Nat) (init : Json) : Json :=
  obj [("name", .str name), ("ty", num ty), ("const", .bool isConst), ("threadlocal", .bool false),
    ("extern", .bool false), ("init", init)]

private def file (name : String) (params : Array Nat) (body : Array Json)
    (globals : Array Json := #[]) (retTy : Nat := 0) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr types), ("params", toJson params), ("ret", num retTy),
    ("body", .arr body), ("globals", .arr globals)]

/-- Targets of the address table. `add2` has a different signature. -/
private def unary (name : String) (op : String) (rhs : Json) : Json :=
  file name #[0] #[arg 0 0 0, inst 1 op 0 #[ref 0, rhs], ret 2 (ref 1)]
private def double := unary "double" "add_wrap" (ref 0)
private def succ := unary "succ" "add_wrap" (lit 1)
private def square := unary "square" "mul_wrap" (ref 0)
private def add2 : Json :=
  file "add2" #[0, 0] #[arg 0 0 0, arg 1 1 0, inst 2 "add_wrap" 0 #[ref 0, ref 1], ret 3 (ref 2)]

private def unaryTable : Array Json := #[fnGlobal "double", fnGlobal "succ", fnGlobal "square"]

/-- `ops[i](x)` over a constant table: every declared target is reachable. -/
private def table : Json :=
  file "table" #[8, 0] #[arg 0 0 8, arg 1 1 0,
    inst 2 "array_elem_val" 2 #[obj [("ty", num 9), ("elems", .arr #[gptr 2 0, gptr 2 1, gptr 2 2])], ref 0],
    call 3 (ref 2) #[ref 1], ret 4 (ref 3)] unaryTable

/-- A call whose callee is the constant address of a named function block. -/
private def constant : Json :=
  file "constant" #[0] #[arg 0 0 0, call 1 (gptr 2 1) #[ref 0], ret 2 (ref 1)] unaryTable

/-- One call through a parameter: the emitted dispatch, in isolation. -/
private def callOnce : Json :=
  file "callOnce" #[2, 0] #[arg 0 0 2, arg 1 1 0, call 2 (ref 0) #[ref 1], ret 3 (ref 2)] unaryTable

/-- `f(f(x))` through a parameter, and its callers passing each target. -/
private def twice : Json :=
  file "twice" #[2, 0] #[arg 0 0 2, arg 1 1 0, call 2 (ref 0) #[ref 1], call 3 (ref 0) #[ref 2],
    ret 4 (ref 3)]
private def viaParam (name : String) (global : Nat) : Json :=
  file name #[0] #[arg 0 0 0,
    call 1 (obj [("ty", num 14), ("func", .str "twice"), ("noreturn", .bool false)]) #[gptr 2 global, ref 0],
    ret 2 (ref 1)] unaryTable

/-- A mutable global whose initializer is a function address, overwritten at runtime. -/
private def globalSlot : Json :=
  file "globalSlot" #[5, 0] #[arg 0 0 5, arg 1 1 0,
    inst 2 "block" 3 #[] [("body", .arr #[inst 7 "cond_br" 4 #[ref 0]
      [("then", .arr #[inst 3 "store" 3 #[gptr 12 3, gptr 2 2], br 8 2]), ("else", .arr #[br 9 2])]])],
    inst 4 "load" 2 #[gptr 12 3], call 5 (ref 4) #[ref 1], ret 6 (ref 5)]
    (unaryTable.push (dataGlobal "slot" false 2 (gptr 2 1)))

/-- A struct field read through a pointer parameter, and a caller that builds the struct. -/
private def field : Json :=
  file "field" #[11, 0] #[arg 0 0 11, arg 1 1 0,
    inst 2 "struct_field_ptr" 15 #[ref 0] [("index", num 0)], inst 3 "load" 2 #[ref 2],
    call 4 (ref 3) #[ref 1], ret 5 (ref 4)]
private def fieldCaller : Json :=
  file "fieldCaller" #[0] #[arg 0 0 0, inst 1 "alloc" 16,
    inst 2 "store" 3 #[ref 1, obj [("ty", num 10), ("elems", .arr #[gptr 2 2, lit 4])]],
    inst 3 "bitcast" 11 #[ref 1],
    call 4 (obj [("ty", num 17), ("func", .str "field"), ("noreturn", .bool false)]) #[ref 3, ref 0],
    ret 5 (ref 4)] unaryTable

/-- A constant global struct whose field initializer is a function address. -/
private def fieldGlobal : Json :=
  file "fieldGlobal" #[0] #[arg 0 0 0,
    call 1 (obj [("ty", num 17), ("func", .str "field"), ("noreturn", .bool false)]) #[gptr 11 3, ref 0],
    ret 2 (ref 1)] (unaryTable.push (dataGlobal "ops" true 10
      (obj [("ty", num 10), ("elems", .arr #[gptr 2 1, lit 4])])))

/-- A function pointer written to and read back from caller memory. -/
private def memory : Json :=
  file "memory" #[12, 0] #[arg 0 0 12, arg 1 1 0, inst 2 "store" 3 #[ref 0, gptr 2 0],
    inst 3 "load" 2 #[ref 0], call 4 (ref 3) #[ref 1], ret 5 (ref 4)] unaryTable

/-- A pointer to a function of another signature, reinterpreted as `*const fn (u32) u32`. -/
private def mismatched : Json :=
  file "mismatched" #[0] #[arg 0 0 0, inst 1 "bitcast" 2 #[gptr 7 0], call 2 (ref 1) #[ref 0],
    ret 3 (ref 2)] #[fnGlobal "add2" 6, fnGlobal "double"]

/-- A data address reinterpreted as a function pointer. -/
private def dataAddress : Json :=
  file "dataAddress" #[0] #[arg 0 0 0, inst 1 "bitcast" 2 #[gptr 13 1], call 2 (ref 1) #[ref 0],
    ret 3 (ref 2)] #[fnGlobal "double", dataGlobal "word" true 0 (lit 5)]

/-- Runtime counterparts: the reinterpreted address reaches `twice` through a parameter,
so no fixed origin is visible at the call and the dispatch throws `.illegal`. -/
private def viaCast (name : String) (source : Json) (globals : Array Json) : Json :=
  file name #[0] #[arg 0 0 0, inst 1 "bitcast" 2 #[source],
    call 2 (obj [("ty", num 14), ("func", .str "twice"), ("noreturn", .bool false)]) #[ref 1, ref 0],
    ret 3 (ref 2)] globals
private def viaMismatch := viaCast "viaMismatch" (gptr 7 3) (unaryTable.push (fnGlobal "add2" 6))
private def viaData := viaCast "viaData" (gptr 13 3) (unaryTable.push (dataGlobal "word" true 0 (lit 5)))
private def viaInt : Json :=
  file "viaInt" #[8, 0] #[arg 0 0 8, arg 1 1 0, inst 2 "bitcast" 2 #[ref 0],
    call 3 (obj [("ty", num 14), ("func", .str "twice"), ("noreturn", .bool false)]) #[ref 2, ref 1],
    ret 4 (ref 3)] unaryTable

/-- A caller-owned stack slot for `memory`. -/
private def memoryCaller : Json :=
  file "memoryCaller" #[0] #[arg 0 0 0, inst 1 "alloc" 12,
    call 2 (obj [("ty", num 18), ("func", .str "memory"), ("noreturn", .bool false)]) #[ref 1, ref 0],
    ret 3 (ref 2)] unaryTable

/-- Static rejections: a fixed callee address that is provably not a function block of the
callee's signature, or a constant that is not a function address. -/
private def constData : Json :=
  file "constData" #[0] #[arg 0 0 0, call 1 (gptr 2 1) #[ref 0], ret 2 (ref 1)]
    #[fnGlobal "double", dataGlobal "word" true 0 (lit 5)]
private def constIncompatible : Json :=
  file "constIncompatible" #[0] #[arg 0 0 0, call 1 (gptr 2 0) #[ref 0], ret 2 (ref 1)]
    #[fnGlobal "add2" 6, fnGlobal "double"]
private def constOffset : Json :=
  file "constOffset" #[0] #[arg 0 0 0, call 1 (gptr 2 0 1) #[ref 0], ret 2 (ref 1)] unaryTable
private def constDataPointer : Json :=
  file "constDataPointer" #[0] #[arg 0 0 0, call 1 (gptr 13 1) #[ref 0], ret 2 (ref 1)]
    #[fnGlobal "double", dataGlobal "word" true 0 (lit 5)]
private def undefCallee : Json :=
  file "undefCallee" #[0] #[arg 0 0 0, call 1 (obj [("ty", num 2), ("undef", .bool true)]) #[ref 0],
    ret 2 (ref 1)] unaryTable

private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)
private def reject (j : Json) (diagnostic : String) : IO Unit :=
  match process j with
  | .ok _ => throw (IO.userError s!"accepted negative case: {diagnostic}")
  | .error e => require ((e.splitOn diagnostic).length > 1) s!"unexpected rejection: {e}"
private def accept (j : Json) : IO Func :=
  match process j with
  | .ok f => pure f
  | .error e => throw (IO.userError e)

/-- Decided observations of the emitted program, appended to the generated file. -/
private def assertions : String := "
deriving instance DecidableEq for Except
def observe (r : Zig.Result (BitVec 32 × Zig.Mem)) : Option (Except Zig.Error Nat) :=
  r.run.map fun e => e.map (·.1.toNat)
-- Every declared target of the table is reachable, through each origin of the pointer.
example : observe ((table 0 5).run mem0) = some (.ok 10) := by decide +kernel
example : observe ((table 1 5).run mem0) = some (.ok 6) := by decide +kernel
example : observe ((table 2 5).run mem0) = some (.ok 25) := by decide +kernel
example : observe ((«constant» 5).run mem0) = some (.ok 6) := by decide +kernel
example : observe ((callOnce ⟨some 2, 0⟩ 5).run mem0) = some (.ok 25) := by decide +kernel
example : observe ((viaDouble 5).run mem0) = some (.ok 20) := by decide +kernel
example : observe ((viaSquare 5).run mem0) = some (.ok 625) := by decide +kernel
example : observe ((globalSlot false 5).run mem0) = some (.ok 6) := by decide +kernel
example : observe ((globalSlot true 5).run mem0) = some (.ok 25) := by decide +kernel
example : observe ((fieldCaller 5).run mem0) = some (.ok 25) := by decide +kernel
example : observe ((fieldGlobal 5).run mem0) = some (.ok 6) := by decide +kernel
example : observe ((memoryCaller 5).run mem0) = some (.ok 10) := by decide +kernel
-- An integer that is the address of a function block is that function.
example : observe ((do viaInt (BitVec.ofInt 64 (← Zig.ptrAddr ⟨some 2, 0⟩)) 5).run mem0) =
    some (.ok 625) := by decide +kernel
-- A target of another signature, a data address and any other address are rejected.
example : observe ((viaMismatch 5).run mem0) = some (.error .illegal) := by decide +kernel
example : observe ((viaData 5).run mem0) = some (.error .illegal) := by decide +kernel
example : observe ((viaInt 0 5).run mem0) = some (.error .illegal) := by decide +kernel
example : observe ((do viaInt (BitVec.ofInt 64 ((← Zig.ptrAddr ⟨some 2, 0⟩) + 1)) 5).run mem0) =
    some (.error .illegal) := by decide +kernel
example : observe ((callOnce ⟨some 3, 0⟩ 5).run mem0) = some (.error .illegal) := by decide +kernel
example : observe ((callOnce ⟨some 0, 1⟩ 5).run mem0) = some (.error .illegal) := by decide +kernel
example : observe ((callOnce ⟨none, 0⟩ 5).run mem0) = some (.error .illegal) := by decide +kernel
"

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Pipeline.lean OUTPUT_DIR")
  let dir := System.FilePath.mk output
  IO.FS.createDirAll dir
  let unknown := "not a function block (an unknown executable address)"
  let incompatible := "has an incompatible signature (called through 'fn (u32) u32')"
  reject mismatched incompatible
  reject constIncompatible incompatible
  reject dataAddress unknown
  reject constData unknown
  reject constOffset unknown
  reject constDataPointer "a constant indirect callee is not a function pointer"
  reject undefCallee "undefined"
  let funcs ← #[double, succ, square, add2, table, constant, callOnce, twice,
    viaParam "viaDouble" 0, viaParam "viaSquare" 2, globalSlot, field, fieldCaller, fieldGlobal, memory,
    memoryCaller, viaMismatch, viaData, viaInt].mapM accept
  match checkProgram funcs with
  | .error e => throw (IO.userError e)
  | .ok _ => pure ()
  -- One table: a constant callee is a callee of the call graph like a runtime pointer.
  let refs := fnRefs funcs
  require (refs == #[("fn (u32) u32", "double"), ("fn (u32) u32", "succ"),
    ("fn (u32) u32", "square"), ("fn (u32, u32) u32", "add2")]) s!"unexpected table {refs}"
  for f in funcs do
    if f.name == "constant" || f.name == "callOnce" then
      require (f.indirectCallees refs == #["double", "succ", "square"])
        s!"{f.name}: indirect callees {f.indirectCallees refs}"
  -- The program check validates each indirect target's signature, also for a constant callee.
  let badSquare := (square.setObjVal! "params" (toJson #[0, 0])).setObjVal! "body"
    (.arr #[arg 0 0 0, arg 1 1 0, inst 2 "mul_wrap" 0 #[ref 0, ref 1], ret 3 (ref 2)])
  match checkProgram (#[← accept badSquare, ← accept constant, ← accept double, ← accept succ]) with
  | .ok _ => throw (IO.userError "accepted a constant-callee target with a mismatched arity")
  | .error e => require ((e.splitOn "callee 'square' has 2 arguments, expected 1").length > 1 ||
      (e.splitOn "has 1 arguments, expected 2").length > 1) s!"unexpected program rejection: {e}"
  IO.FS.writeFile (dir / "Calls.lean") (emit funcs "Calls" "" ++ "\nnamespace Calls\n" ++
    assertions ++ "end Calls\n")
  IO.println "indirect call synthetic regressions passed"
