import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Synthetic schema/checker/emitter cases. The root driver elaborates emitted proofs. -/
open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def lit (n : Nat) : Json := obj [("ty", num 0), ("val", .str (toString n))]
private def ptr (child : Nat) (isConst : Bool := false) : Json :=
  obj [("k", .str "ptr"), ("size", .str "one"), ("const", .bool isConst),
    ("child", num child), ("ptr_align", num 4), ("abi_size", num 8), ("abi_align", num 8)]
private def structTy (name : String) (fields : Array (String × Nat)) (size : Nat) : Json :=
  obj [("k", .str "struct"), ("name", .str name), ("layout", .str "auto"),
    ("abi_size", num size), ("abi_align", num 4),
    ("fields", .arr (fields.mapIdx fun idx (name, ty) =>
      obj [("name", .str name), ("ty", num ty), ("offset", num (idx * 4))]))]
private def types : Array Json := #[
  obj [("k", .str "int"), ("signed", .bool false), ("bits", num 32), ("abi_size", num 4), ("abi_align", num 4)],
  obj [("k", .str "void")], obj [("k", .str "noreturn")],
  structTy "Pair" #[("x", 0), ("y", 0)] 8, ptr 3, ptr 0,
  structTy "Outer" #[("tag", 0), ("inner", 3)] 12, ptr 6, ptr 0 true, ptr 3 true,
  structTy "Other" #[("x", 0), ("y", 0)] 8, ptr 10,
  obj [("k", .str "array"), ("len", num 2), ("child", num 3), ("sentinel", .bool false),
    ("abi_size", num 16), ("abi_align", num 4)], ptr 12,
  structTy "Bag" #[("tag", 0), ("items", 12)] 20, ptr 14,
  obj [("k", .str "int"), ("signed", .bool false), ("bits", num 64), ("abi_size", num 8), ("abi_align", num 8)]]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def field (id base index : Nat) (ty : Nat := 5) : Json :=
  inst id "struct_field_ptr" ty #[ref base] [("index", num index)]
private def parent (id base index : Nat) (ty : Nat := 4) : Json :=
  inst id "field_parent_ptr" ty #[ref base] [("index", num index)]
private def file (name : String) (body : Array Json) (ts : Array Json := types) (ret : Nat := 0) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr ts), ("params", .arr #[]), ("ret", num ret), ("body", .arr body)]
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
private def writeCase (dir : System.FilePath) (name : String) (j : Json) (expected : Nat) : IO Unit := do
  let f ← match process j with | .ok f => pure f | .error e => throw (IO.userError e)
  require (escapingAllocs f).isEmpty s!"{name}: local unexpectedly escaped"
  require (!f.usesMemoryLocally) s!"{name}: local recovery unexpectedly uses memory"
  let source := emit #[f] "LocalParent" ""
  require ((source.splitOn "panic!").length == 1) s!"{name}: lost local place"
  require ((source.splitOn "Zig.alloc").length == 1) s!"{name}: local heap/stack lowering"
  IO.FS.writeFile (dir / s!"{name}.lean") (source ++
    "\nderiving instance DecidableEq for Except\n" ++
    s!"example : (LocalParent.{name}.map BitVec.toNat).run = some (.ok {expected}) := by decide +kernel\n")

/-- A local whose place escapes (an array element, `ptr_elem_ptr`) is a stack block: parent
recovery subtracts the exported field offset and aliases the original block (L11). -/
private def writeMemoryCase (dir : System.FilePath) (name : String) (j : Json) (expected : Nat) :
    IO Unit := do
  let f ← match process j with | .ok f => pure f | .error e => throw (IO.userError e)
  require (!(escapingAllocs f).isEmpty) s!"{name}: array-element local unexpectedly stayed a place"
  let source := emit #[f] "LocalParent" ""
  require ((source.splitOn "panic!").length == 1) s!"{name}: lost memory recovery"
  IO.FS.writeFile (dir / s!"{name}.lean") (source ++
    "\nderiving instance DecidableEq for Except\n" ++
    s!"example : ((LocalParent.{name}.run \{}).run.map fun r => r.map (·.1.toNat)) = some (.ok {expected}) := by decide +kernel\n")

private def setup : Array Json := #[inst 10 "alloc" 4,
  field 11 10 0, inst 12 "store" 1 #[ref 11, lit 3],
  field 13 10 1, inst 14 "store" 1 #[ref 13, lit 9]]
private def finish (read : Nat) : Array Json :=
  #[inst 80 "load" 0 #[ref read], inst 81 "ret" 2 #[ref 80]]

/-- Runtime lookup regression, not a theorem: the hash-map cache keeps the first source
instruction type for a bare duplicate-ID caller. The exact provenance observation is retained. -/
private def checkFirstOccurrence : IO Unit := do
  let ts : Array Ty := #[.int false 32, .struct "Pair" "auto" #[("x", 0), ("y", 0)],
    .ptr "one" false 0, .ptr "one" false 1,
    .struct "Outer" "auto" #[("inner", 1)], .ptr "one" false 4]
  let ls : Array Layout := Array.replicate ts.size {}
  let observed := ((localPlacePaths ts ls #[
    { id := 10, ty := 3, op := .alloc },
    { id := 10, ty := 0, op := .load (.inst 10) },
    { id := 11, ty := 2, op := .fieldPtr (.inst 10) 0 },
    { id := 12, ty := 3, op := .fieldParentPtr (.inst 11) 0 }]).find? (·.1 == 12)).map
      (fun (_, path) => path.size)
  require (observed == some 0) "runtime first-occurrence lookup regression failed"

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Pipeline.lean OUTPUT_DIR")
  let dir := System.FilePath.mk output
  IO.FS.createDirAll dir
  checkFirstOccurrence
  writeCase dir "direct" (file "direct" (setup ++ #[parent 20 11 0,
    field 21 20 1, inst 22 "store" 1 #[ref 21, lit 42]] ++ finish 13)) 42
  -- Same-type fields make an index mismatch observable even without a child mismatch.
  writeCase dir "secondField" (file "secondField" (setup ++ #[parent 20 13 1,
    field 21 20 0, inst 22 "store" 1 #[ref 21, lit 17]] ++ finish 11)) 17
  writeCase dir "castAlias" (file "castAlias" (setup ++ #[
    inst 19 "bitcast" 8 #[ref 11], parent 20 19 0 9,
    inst 21 "bitcast" 4 #[ref 20], field 22 21 1,
    inst 23 "store" 1 #[ref 22, lit 33]] ++ finish 13)) 33
  let nested := #[inst 10 "alloc" 7, field 11 10 1 4, field 12 11 0,
    inst 13 "store" 1 #[ref 12, lit 2], field 14 11 1,
    inst 15 "store" 1 #[ref 14, lit 9], parent 20 14 1,
    field 21 20 0, inst 22 "store" 1 #[ref 21, lit 27],
    parent 30 20 1 7, field 31 30 0, inst 32 "store" 1 #[ref 31, lit 6],
    inst 33 "load" 0 #[ref 12], inst 34 "load" 0 #[ref 31],
    inst 35 "add_wrap" 0 #[ref 33, ref 34], inst 36 "ret" 2 #[ref 35]]
  writeCase dir "nested" (file "nested" nested) 33
  -- `bag.items[1].b` recovers `bag.items[1]` (a memory parent inside an array inside a
  -- struct); `bag.items` recovers `bag`. Writes through both parents alias `bag`.
  writeMemoryCase dir "arrayItem" (file "arrayItem" #[inst 10 "alloc" 15,
    field 11 10 0, inst 12 "store" 1 #[ref 11, lit 1], field 13 10 1 13,
    inst 14 "ptr_elem_ptr" 4 #[ref 13, obj [("ty", num 16), ("val", .str "1")]],
    field 15 14 0, inst 16 "store" 1 #[ref 15, lit 3],
    field 17 14 1, inst 18 "store" 1 #[ref 17, lit 9],
    parent 20 17 1, field 21 20 0, inst 22 "store" 1 #[ref 21, lit 27],
    parent 30 13 1 15, field 31 30 0, inst 32 "store" 1 #[ref 31, lit 6],
    inst 40 "load" 0 #[ref 15], inst 41 "load" 0 #[ref 11], inst 42 "load" 0 #[ref 17],
    inst 43 "add_wrap" 0 #[ref 40, ref 41], inst 44 "add_wrap" 0 #[ref 43, ref 42],
    inst 45 "ret" 2 #[ref 44]]) 42
  -- Recovery through memory from the first field: `items[0].a` to `items[0]`, then `.b`.
  writeMemoryCase dir "arrayFirst" (file "arrayFirst" #[inst 10 "alloc" 15,
    field 13 10 1 13, inst 14 "ptr_elem_ptr" 4 #[ref 13, obj [("ty", num 16), ("val", .str "0")]],
    field 15 14 0, inst 16 "store" 1 #[ref 15, lit 5], field 17 14 1, inst 18 "store" 1 #[ref 17, lit 7],
    parent 20 15 0, field 21 20 1, inst 22 "store" 1 #[ref 21, lit 11],
    inst 40 "load" 0 #[ref 17], inst 41 "load" 0 #[ref 15],
    inst 42 "add_wrap" 0 #[ref 40, ref 41], inst 45 "ret" 2 #[ref 42]]) 16
  let bad := fun (p : Json) (ts : Array Json) => file "bad" (setup ++ #[p] ++ finish 13) ts
  let matching := "requires the matching terminal ordinary struct field"
  reject (bad (parent 20 11 1) types) matching
  reject (bad (parent 20 11 8) types) matching
  reject (bad (parent 20 11 0 11) types) matching
  reject (bad (parent 20 11 0 5) types) matching
  reject (bad (parent 20 10 0) types) matching
  reject (bad (parent 20 11 0 0) types) matching
  reject (file "sliceField" #[inst 10 "alloc" 4,
    inst 11 "ptr_slice_len_ptr" 5 #[ref 10], parent 20 11 0] types)
    matching
  reject (file "escapedBadIndex" (setup ++ #[parent 20 11 1, inst 21 "ret" 2 #[ref 20]]) types 4)
    matching
  let packed := types.set! 3 ((types[3]!).setObjVal! "layout" (.str "packed"))
  reject (bad (parent 20 11 0) packed) matching
  let union := types.set! 3 (obj [("k", .str "union"), ("name", .str "U"),
    ("layout", .str "auto"), ("tag", num 17),
    ("fields", .arr #[obj [("name", .str "x"), ("ty", num 0)], obj [("name", .str "y"), ("ty", num 0)]])])
    |>.push (obj [("k", .str "enum"), ("name", .str "Tag"), ("tag", num 0),
      ("exhaustive", .bool true), ("fields", .arr #[obj [("name", .str "x"), ("value", .str "0")],
        obj [("name", .str "y"), ("value", .str "1")]])])
  reject (bad (parent 20 11 0) union) matching
  let bits := types.set! 5 ((((types[5]!).setObjVal! "host_size" (num 4)).setObjVal! "bit_offset" (num 0)).setObjVal! "vector_index" .null)
  reject (bad (parent 20 11 0) bits) matching
  let mismatch := types.set! 5 ((types[5]!).setObjVal! "child" (num 1))
  reject (bad (parent 20 11 0) mismatch) matching
  reject (file "castMismatch" (setup ++ #[inst 19 "bitcast" 4 #[ref 11], parent 20 19 0] ++ finish 13))
    "needs a proven terminal struct field"
  -- A returned recovered pointer must propagate escape back to the original alloc.
  let escaped := file "escaped" (setup ++ #[parent 20 11 0, inst 21 "ret" 2 #[ref 20]]) types 4
  let f ← match process escaped with | .ok f => pure f | .error e => throw (IO.userError e)
  -- `process` canonicalizes and renumbers: the first raw alloc (10) becomes alloc 0.
  require (escapingAllocs f == #[0]) "recovered parent lost alloc escape provenance"
  IO.println "local parent synthetic regressions passed"
