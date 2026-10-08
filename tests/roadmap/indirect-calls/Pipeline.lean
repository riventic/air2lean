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
  fnTy "fn (*const Ops, u32) u32"]

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

private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Pipeline.lean OUTPUT_DIR")
  let dir := System.FilePath.mk output
  IO.FS.createDirAll dir
  let all := #[double, succ, square, add2, table, constant, twice, viaParam "viaDouble" 0,
    viaParam "viaSquare" 2, globalSlot, field, fieldCaller, memory, mismatched, dataAddress]
  let mut funcs := #[]
  for j in all do
    match process j with
    | .ok f => funcs := funcs.push f
    | .error e => IO.println s!"REJECT: {e}"
  match checkProgram funcs with
  | .error e => IO.println s!"PROGRAM REJECT: {e}"
  | .ok _ => pure ()
  IO.FS.writeFile (dir / "Calls.lean") (emit funcs "Calls" "")
