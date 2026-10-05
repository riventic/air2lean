import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Checked AIR → emitted Lean semantic regressions. This driver only writes source files.
Run `lake env lean --run tests/review/Emitter.lean OUTPUT_DIR`, then elaborate each output
separately. Keeping compilation outside the driver allows serialized, monitored validation. -/

open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (id : Nat) : Json := obj [("inst", num id)]
private def lit (ty : Nat) (v : String) : Json := obj [("ty", num ty), ("val", .str v)]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def intTy (bits : Nat) : Json :=
  obj [("k", .str "int"), ("signed", .bool false), ("bits", num bits),
    ("abi_size", num (Zig.intSize bits)), ("abi_align", num (Zig.intAlign bits))]
private def ptrTy (child : Nat) (const_ : Bool := false) (size : String := "one") : Json :=
  obj [("k", .str "ptr"), ("size", .str size), ("const", .bool const_), ("child", num child),
    ("ptr_align", num 1), ("abi_size", num (if size == "slice" then 16 else 8)), ("abi_align", num 8)]
private def voidTy : Json := obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)]
private def nrTy : Json := obj [("k", .str "noreturn")]
private def field (name : String) (ty : Nat) : Json := obj [("name", .str name), ("ty", num ty)]
private def tupleTy (fields : Array Nat) : Json :=
  obj [("k", .str "tuple"), ("fields", .arr (fields.map fun t => obj [("ty", num t)]))]
private def enumTy (name : String) (tag : Nat) (fields : Array String) : Json :=
  obj [("k", .str "enum"), ("name", .str name), ("tag", num tag), ("exhaustive", .bool true),
    ("fields", .arr (fields.mapIdx fun i n => obj [("name", .str n), ("value", .str (toString i))])),
    ("abi_size", num 1), ("abi_align", num 1)]
private def file (name : String) (types : Array Json) (params : Array Nat) (ret : Nat)
    (body : Array Json) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr types), ("params", toJson params), ("ret", num ret),
    ("body", .arr body)]
private def accept (j : Json) : IO Func := do
  match (do let f ← normalize (← Raw.parseFunc j); check f; pure f : Except String Func) with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def writeCase (directory : System.FilePath) (name : String) (files : Array Json)
    (assertions : String) (mode : FloatSemantics := .ieee) : IO Unit := do
  let funcs ← files.mapM accept
  match checkProgram funcs with
  | .error e => throw (IO.userError e)
  | .ok _ => pure ()
  IO.FS.writeFile (directory / (name ++ ".lean"))
    (emit funcs "Review" "" mode ++
      "\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption\n" ++
      "private def failedWith {α : Type} (r : Zig.Result α) (expected : Zig.Error) : Bool := match r.run with | some (.error e) => decide (e = expected) | _ => false\n" ++
      assertions ++ "\n")

/-- Mirrors both 0.16 forms: an addressable parameter copy, and a mutable local. The
destination load must read only two bytes; forwarding it as the stored u32 is unsound. -/
private def pointerRead (name : String) (mutable_ : Bool) : Json :=
  file name #[intTy 32, intTy 16, ptrTy 0, ptrTy 1 true, voidTy, nrTy] #[0] 0
    (#[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "alloc" 2,
      inst 30 "store" 4 #[ref 20, ref 10]] ++
      (if mutable_ then #[inst 35 "store" 4 #[ref 20, ref 10]] else #[]) ++
      #[inst 40 "bitcast" 3 #[ref 20], inst 50 "load" 1 #[ref 40],
        inst 60 "intcast" 0 #[ref 50], inst 70 "ret" 5 #[ref 60]])

private def pointerWrite : Json :=
  file "pointerWrite" #[intTy 32, intTy 16, ptrTy 0, ptrTy 1, voidTy, nrTy] #[0] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "alloc" 2,
      inst 30 "store" 4 #[ref 20, ref 10], inst 40 "bitcast" 3 #[ref 20],
      inst 50 "store" 4 #[ref 40, lit 1 "43981"], inst 60 "load" 0 #[ref 20],
      inst 70 "ret" 5 #[ref 60]]

private def sameChild : Json :=
  file "sameChild" #[intTy 32, ptrTy 0, ptrTy 0 true, voidTy, nrTy] #[0] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "alloc" 1,
      inst 30 "store" 3 #[ref 20, ref 10], inst 40 "bitcast" 2 #[ref 20],
      inst 50 "load" 0 #[ref 40], inst 60 "ret" 4 #[ref 50]]

private def tupleProjectionFile (name : String) (fields : Nat) (index : Nat) : Json :=
  file name #[intTy 8, tupleTy (Array.replicate fields 0), nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)],
      inst 1 "struct_field_val" 0 #[ref 0] [("index", num index)], inst 2 "ret" 2 #[ref 1]]

private def emptyPacked : Json :=
  file "emptyPacked" #[obj [("k", .str "struct"), ("name", .str "Empty"),
    ("layout", .str "packed"), ("fields", .arr #[])], nrTy] #[] 0
    #[inst 0 "ret" 1 #[obj [("ty", num 0), ("elems", .arr #[])]]]

private def enumHelpers : Json :=
  file "enumHelpers" #[intTy 8,
    enumTy "E" 0 #["toBits", "ofInt?", "isNamed", "tagName", "mk", "rec"], nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "intcast" 0 #[ref 0], inst 2 "ret" 2 #[ref 1]]

private def structMembers : Json :=
  file "structMembers" #[intTy 8, obj [("k", .str "struct"), ("name", .str "S"),
    ("layout", .str "auto"), ("fields", .arr #[field "mk" 0, field "rec" 0, field "a-b" 0])], nrTy]
    #[1] 0 #[inst 0 "arg" 1 #[] [("param", num 0)],
      inst 1 "struct_field_val" 0 #[ref 0] [("index", num 2)], inst 2 "ret" 2 #[ref 1]]

private def identityFile (name : String) : Json :=
  file name #[intTy 8, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "ret" 1 #[ref 0]]

private def localNames : Json :=
  file "localNames" #[intTy 8, ptrTy 0, voidTy, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "alloc" 1, inst 2 "alloc" 1,
      inst 3 "dbg_var_ptr" 2 #[ref 1] [("name", .str "mk")],
      inst 4 "dbg_var_ptr" 2 #[ref 2] [("name", .str "mk")],
      inst 5 "store" 2 #[ref 1, ref 0], inst 6 "store" 2 #[ref 2, lit 0 "7"],
      inst 7 "load" 0 #[ref 1], inst 8 "load" 0 #[ref 2],
      inst 9 "add" 0 #[ref 7, ref 8], inst 10 "ret" 3 #[ref 9]]

private def indirectLoop : Json :=
  (file "indirectLoop" #[intTy 32, obj [("k", .str "other"), ("name", .str "fn (u32) u32")],
    ptrTy 1 true, voidTy, nrTy] #[0] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)],
      inst 20 "block" 2 #[] [("body", .arr #[inst 30 "br" 4
        #[obj [("ty", num 2), ("ptr", obj [("global", num 0), ("off", num 0)])]] [("target", num 20)]])],
      inst 40 "loop" 4 #[] [("body", .arr #[inst 50 "call" 0 #[ref 10] [("callee", ref 20)],
        inst 60 "cond_br" 4 #[obj [("ty", num 5), ("val", .str "true")]]
          [("then", .arr #[inst 70 "ret" 4 #[ref 50]]),
           ("else", .arr #[inst 80 "repeat" 4 #[] [("target", num 40)]])]])]])
    |>.setObjVal! "types" (.arr #[intTy 32,
      obj [("k", .str "other"), ("name", .str "fn (u32) u32")], ptrTy 1 true, voidTy, nrTy,
      obj [("k", .str "bool")]])
    |>.setObjVal! "globals" (.arr #[obj [("name", .str "target"), ("ty", num 1), ("const", .bool true),
      ("init", obj [("ty", num 1), ("func", .str "target")])]])

private def target : Json :=
  file "target" #[intTy 32, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "add" 0 #[ref 0, lit 0 "1"],
      inst 2 "ret" 1 #[ref 1]]

/-- The conservative flow summary does not certify loops. Untargeted blocks still
must propagate the loop's exit without matching a nonexistent block constructor. -/
private def blockLoopVoid : Json :=
  file "blockLoopVoid" #[voidTy, nrTy] #[] 0
    #[inst 0 "block" 0 #[] [("body", .arr #[inst 1 "loop" 1 #[]
      [("body", .arr #[inst 2 "ret" 1 #[lit 0 "{}"]])]])],
      inst 3 "ret" 1 #[lit 0 "{}"]]

private def blockLoopValue : Json :=
  file "blockLoopValue" #[intTy 8, voidTy, nrTy] #[] 0
    #[inst 0 "block" 0 #[] [("body", .arr #[inst 1 "loop" 2 #[]
      [("body", .arr #[inst 2 "ret" 2 #[lit 0 "17"]])]])],
      inst 3 "ret" 2 #[lit 0 "99"]]

/-- The inner void block owns no branch, but the outer value block consumes its exit. -/
private def blockLoopOuter : Json :=
  file "blockLoopOuter" #[intTy 8, voidTy, nrTy] #[] 0
    #[inst 0 "block" 0 #[] [("body", .arr #[inst 1 "block" 1 #[]
      [("body", .arr #[inst 2 "loop" 2 #[] [("body", .arr
        #[inst 3 "br" 2 #[lit 0 "38"] [("target", num 0)]])]])], inst 4 "trap" 2])],
      inst 5 "ret" 2 #[ref 0]]

/-- A real own-target branch must still resume the block's continuation. -/
private def blockLoopResume : Json :=
  file "blockLoopResume" #[intTy 8, voidTy, nrTy] #[] 0
    #[inst 0 "block" 1 #[] [("body", .arr #[inst 1 "loop" 2 #[]
      [("body", .arr #[inst 2 "br" 2 #[lit 1 "{}"] [("target", num 0)]])]])],
      inst 3 "ret" 2 #[lit 0 "23"]]

private def tagLoop : Json :=
  file "tagLoop" #[intTy 32, intTy 8, enumTy "ET" 1 #["a", "b"],
    obj [("k", .str "union"), ("name", .str "UT"), ("layout", .str "auto"), ("tag", num 2),
      ("fields", .arr #[field "a" 0, field "b" 0]), ("abi_size", num 8), ("abi_align", num 4)],
    ptrTy 3, voidTy, nrTy, obj [("k", .str "bool")]] #[4, 2] 3
    #[inst 10 "arg" 4 #[] [("param", num 0)], inst 20 "arg" 2 #[] [("param", num 1)],
      inst 25 "block" 2 #[] [("body", .arr #[inst 26 "br" 6 #[ref 20] [("target", num 25)]])],
      inst 30 "loop" 6 #[] [("body", .arr #[inst 40 "set_union_tag" 5 #[ref 10, ref 25],
        inst 45 "load" 3 #[ref 10], inst 50 "cond_br" 6 #[lit 7 "true"]
          [("then", .arr #[inst 60 "ret" 6 #[ref 45]]),
           ("else", .arr #[inst 70 "repeat" 6 #[] [("target", num 30)]])]])]]

private def spawnSlice : Json :=
  (file "spawnSlice" #[intTy 8, ptrTy 0 true "slice", tupleTy #[1], voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread")],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 5)],
    obj [("k", .str "struct"), ("name", .str "Thread.SpawnConfig"),
      ("layout", .str "auto"), ("fields", .arr #[]), ("abi_size", num 0), ("abi_align", num 1)]] #[1] 3
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "aggregate_init" 2 #[ref 0],
      inst 2 "call" 7 #[obj [("ty", num 8), ("elems", .arr #[])], ref 1]
        [("callee", obj [("func", .str "Thread.spawn"), ("comptime_fn", .str "sliceWorker")])],
      inst 3 "unwrap_errunion_payload" 5 #[ref 2],
      inst 4 "call" 3 #[ref 3] [("callee", obj [("func", .str "Thread.join")])],
      inst 5 "ret" 4 #[lit 3 "{}"]])
    |>.setObjVal! "globals" (.arr #[obj [("ty", num 0), ("const", .bool true), ("init", lit 0 "42")]])

private def sliceWorker : Json :=
  file "sliceWorker" #[intTy 8, ptrTy 0 true "slice", intTy 64, nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "slice_elem_val" 0 #[ref 0, lit 2 "0"],
      inst 2 "ret" 3 #[ref 1]]

private def floatConversion : Json :=
  file "floatConversion" #[obj [("k", .str "float"), ("bits", num 80)],
    obj [("k", .str "float"), ("bits", num 16)], nrTy] #[0] 1
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "fptrunc" 1 #[ref 0], inst 2 "ret" 2 #[ref 1]]

private def legacyUnion : Json :=
  file "legacyUnion" #[intTy 32, obj [("k", .str "union"), ("name", .str "U"),
    ("layout", .str "extern"), ("fields", .arr #[field "x" 0]), ("abi_size", num 4), ("abi_align", num 4)],
    ptrTy 1, voidTy, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "alloc" 2,
      inst 2 "union_init" 1 #[ref 0] [("index", num 0)], inst 3 "store" 3 #[ref 1, ref 2],
      inst 4 "set_union_tag" 3 #[ref 1, lit 0 "0"], inst 5 "load" 1 #[ref 1],
      inst 6 "struct_field_val" 0 #[ref 5] [("index", num 0)], inst 7 "ret" 4 #[ref 6]]

/-- The failed first comparison can leave its block through a nested branch. It must not
establish a fact used to remove the second safety check. -/
private def escapingSafetyCheck : Json :=
  file "escapingSafetyCheck" #[intTy 8, obj [("k", .str "bool")], voidTy, nrTy] #[0, 0, 1] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "arg" 0 #[] [("param", num 1)],
      inst 30 "arg" 1 #[] [("param", num 2)], inst 40 "cmp_lte" 1 #[ref 10, ref 20],
      inst 50 "block" 2 #[] [("body", .arr #[inst 60 "cond_br" 3 #[ref 40]
        [("then", .arr #[inst 70 "br" 3 #[lit 2 "{}"] [("target", num 50)]]),
         ("else", .arr #[inst 80 "cond_br" 3 #[ref 30]
           [("then", .arr #[inst 90 "br" 3 #[lit 2 "{}"] [("target", num 50)]]),
            ("else", .arr #[inst 100 "trap" 3])], inst 110 "unreach" 3])]])],
      inst 120 "cmp_lte" 1 #[ref 10, ref 20],
      inst 130 "block" 2 #[] [("body", .arr #[inst 140 "cond_br" 3 #[ref 120]
        [("then", .arr #[inst 150 "br" 3 #[lit 2 "{}"] [("target", num 130)]]),
         ("else", .arr #[inst 160 "trap" 3])]])], inst 170 "ret" 3 #[lit 0 "7"]]

private def structTypeShadow : Json :=
  file "structTypeShadow" #[intTy 8,
    obj [("k", .str "struct"), ("name", .str "T"), ("layout", .str "auto"),
      ("fields", .arr #[field "value" 0])],
    obj [("k", .str "struct"), ("name", .str "Binders"), ("layout", .str "auto"),
      ("fields", .arr #[field "BitVec" 0, field "next" 0, field "T" 0, field "tail" 1])], nrTy]
    #[2] 0 #[inst 0 "arg" 2 #[] [("param", num 0)],
      inst 1 "struct_field_val" 1 #[ref 0] [("index", num 3)],
      inst 2 "struct_field_val" 0 #[ref 1] [("index", num 0)], inst 3 "ret" 3 #[ref 2]]

private def localTypeShadow : Json :=
  file "localTypeShadow" #[intTy 8,
    obj [("k", .str "struct"), ("name", .str "T"), ("layout", .str "auto"),
      ("fields", .arr #[field "value" 0])], ptrTy 0, ptrTy 1, voidTy, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 10 "alloc" 2,
      inst 11 "dbg_var_ptr" 4 #[ref 10] [("name", .str "BitVec")],
      inst 20 "alloc" 2, inst 21 "dbg_var_ptr" 4 #[ref 20] [("name", .str "T")],
      inst 30 "alloc" 3, inst 31 "dbg_var_ptr" 4 #[ref 30] [("name", .str "tail")],
      inst 40 "store" 4 #[ref 10, ref 0], inst 41 "store" 4 #[ref 20, ref 0],
      inst 42 "aggregate_init" 1 #[ref 0], inst 43 "store" 4 #[ref 30, ref 42],
      inst 50 "load" 1 #[ref 30], inst 60 "struct_field_val" 0 #[ref 50] [("index", num 0)],
      inst 70 "ret" 5 #[ref 60]]

private def ctorIndexName : Json :=
  file "ctorIndexName" #[intTy 8, enumTy "CtorNames" 0
    #["ctorIdx", "ctorElim", "ctorElimType", "sparseCasesOn"], nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "intcast" 0 #[ref 0], inst 2 "ret" 2 #[ref 1]]

private def packedInstanceName : Json :=
  file "packedInstanceName" #[intTy 8,
    obj [("k", .str "struct"), ("name", .str "P"), ("layout", .str "packed"),
      ("fields", .arr #[field "x" 0]), ("abi_size", num 1), ("abi_align", num 1)],
    ptrTy 1, nrTy] #[2] 1
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "load" 1 #[ref 0], inst 2 "ret" 3 #[ref 1]]

/-- Fixed helper binders (`v`, `g`) and indexed function binders (`p0`) must not
shadow a source type in another parameter, a result type, or a helper body. -/
private def enumBinderType : Json :=
  file "enumBinderType" #[intTy 8, enumTy "v" 0 #["a", "b"], nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "intcast" 0 #[ref 0], inst 2 "ret" 2 #[ref 1]]

private def parameterBinderType : Json :=
  file "parameterBinderType" #[intTy 8,
    obj [("k", .str "struct"), ("name", .str "p0"), ("layout", .str "auto"),
      ("fields", .arr #[field "value" 0])], nrTy] #[1] 1
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "ret" 2 #[ref 0]]

private def unionBinderType : Json :=
  file "unionBinderType" #[intTy 8, enumTy "GTag" 0 #["a", "b"],
    obj [("k", .str "union"), ("name", .str "g"), ("layout", .str "auto"), ("tag", num 1),
      ("fields", .arr #[field "a" 0, field "b" 0])], nrTy] #[2] 0
    #[inst 0 "arg" 2 #[] [("param", num 0)],
      inst 1 "struct_field_val" 0 #[ref 0] [("index", num 0)], inst 2 "ret" 3 #[ref 1]]

/-- A named type used after a scalar result or a value-producing block must avoid
that result's local spelling, including a discarded scalar result. -/
private def instructionBinderType (name : String) (used : Bool) : Json :=
  file (if used then "instructionBinderType" else "unusedBinderType") #[intTy 8,
    obj [("k", .str "struct"), ("name", .str name), ("layout", .str "auto"),
      ("fields", .arr #[field "value" 0])], nrTy] #[0] 1
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "intcast" 0 #[ref 0],
      inst 2 "aggregate_init" 1 #[ref (if used then 1 else 0)], inst 3 "ret" 2 #[ref 2]]

private def blockBinderType : Json :=
  file "blockBinderType" #[intTy 8,
    obj [("k", .str "struct"), ("name", .str "v1"), ("layout", .str "auto"),
      ("fields", .arr #[field "value" 0])], nrTy] #[0] 1
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "block" 0 #[]
      [("body", .arr #[inst 2 "br" 2 #[ref 0] [("target", num 1)]])],
      inst 3 "aggregate_init" 1 #[ref 1], inst 4 "ret" 2 #[ref 3]]

/-- The callee spelling must stay distinct from the caller's generated `p0` value. -/
private def functionBinderCall : Json :=
  file "functionBinderCall" #[intTy 8, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)],
      inst 1 "call" 0 #[ref 0] [("callee", obj [("func", .str "p0")])], inst 2 "ret" 1 #[ref 1]]

/-- A Zig identifier that is a Lean parser keyword needs quoting in both declaration
and projection positions. The function call also uses the allocated quoted spelling. -/
private def keywordField (keyword : String) : Json :=
  file s!"keywordField_{keyword}" #[intTy 8,
    obj [("k", .str "struct"), ("name", .str s!"KeywordField_{keyword}"), ("layout", .str "auto"),
      ("fields", .arr #[field keyword 0])], nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)],
      inst 1 "struct_field_val" 0 #[ref 0] [("index", num 0)],
      inst 2 "call" 0 #[ref 1] [("callee", obj [("func", .str keyword)])], inst 3 "ret" 2 #[ref 2]]

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Emitter.lean OUTPUT_DIR")
  let directory : System.FilePath := output
  IO.FS.createDirAll directory
  let constRead ← accept (pointerRead "pointerConst" false)
  let varRead ← accept (pointerRead "pointerVar" true)
  require (!(escapingAllocs constRead).isEmpty && !(escapingAllocs varRead).isEmpty)
    "differing-pointee local cast did not escape to byte memory"
  require ((escapingAllocs (← accept sameChild)).isEmpty) "same-pointee const copy unnecessarily escaped"
  writeCase directory "pointerCasts" #[pointerRead "pointerConst" false, pointerRead "pointerVar" true, pointerWrite, sameChild]
    "example : successful (((Review.pointerConst 0x12345678).run {}).map fun (v, _) => v.toNat) = some 0x5678 := by native_decide\nexample : successful (((Review.pointerVar 0x12345678).run {}).map fun (v, _) => v.toNat) = some 0x5678 := by native_decide\nexample : successful (((Review.pointerWrite 0x12345678).run {}).map fun (v, _) => v.toNat) = some 0x1234abcd := by native_decide\nexample : successful ((Review.sameChild 0x12345678).map BitVec.toNat) = some 0x12345678 := by native_decide"
  writeCase directory "tuples" #[tupleProjectionFile "tupleLast" 4 3, tupleProjectionFile "tupleFirst" 4 0, tupleProjectionFile "tupleSingle" 1 0, emptyPacked]
    "example : successful ((Review.tupleLast (11, 22, 33, 44)).map BitVec.toNat) = some 44 := by native_decide\nexample : successful ((Review.tupleFirst (11, 22, 33, 44)).map BitVec.toNat) = some 11 := by native_decide\nexample : successful ((Review.tupleSingle 19).map BitVec.toNat) = some 19 := by native_decide\nexample : successful (Review.emptyPacked.map fun v => (Zig.Packed.toBits v).toNat) = some 0 := by native_decide"
  writeCase directory "names" #[enumHelpers, structMembers, localNames, identityFile "BitVec", identityFile "dup?", identityFile "dup!", identityFile "enumHelpersLocals"]
    "example : successful ((Review.enumHelpers Review.E.toBits).map BitVec.toNat) = some 0 := by native_decide\nexample : successful ((Review.enumHelpers Review.E.rec_air2lean1).map BitVec.toNat) = some 5 := by native_decide\nexample : successful ((Review.structMembers { mk_air2lean1 := 1, rec_air2lean1 := 2, «a-b» := 3 }).map BitVec.toNat) = some 3 := by native_decide\nexample : successful ((Review.localNames 3).map BitVec.toNat) = some 10 := by native_decide"
  writeCase directory "indirectCapture" #[indirectLoop, target]
    "example : successful (((Review.indirectLoop 4).run Review.mem0).map fun (v, _) => v.toNat) = some 5 := by native_decide"
  for j in #[blockLoopVoid, blockLoopValue] do
    let f ← accept j
    require ((brTargets f.allInsts).isEmpty &&
      !(controlFlowSummaries f.body).outwardBlocks[0]?.getD false)
      "untargeted loop fixture lost its conservative-summary boundary"
    let cached := mkFCtx f #[] #[] .ieee #[] #[]
    let bare := { cached with branchTargetSet := none, outwardBlocks := {} }
    require (emitStmts bare #[] f.body.toList == emitStmts cached #[] f.body.toList)
      "untargeted loop exit depends on a prepared branch or summary cache"
  writeCase directory "blockLoopExits" #[blockLoopVoid, blockLoopValue, blockLoopOuter, blockLoopResume]
    "example : successful Review.blockLoopVoid = some () := by native_decide\nexample : successful (Review.blockLoopValue.map BitVec.toNat) = some 17 := by native_decide\nexample : successful (Review.blockLoopOuter.map BitVec.toNat) = some 38 := by native_decide\nexample : successful (Review.blockLoopResume.map BitVec.toNat) = some 23 := by native_decide"
  writeCase directory "unionTagCapture" #[tagLoop]
    "example : successful ((((do let p ← Zig.allocStack 8 4; Zig.store 4 p (Review.UT.a 17); Review.tagLoop p Review.ET.b) : Zig.MemM Review.UT).run {}).map fun (v, _) => match v with | .a _ => 0 | .b n => n.toNat) = some 17 := by native_decide"
  writeCase directory "spawnedSlice" #[spawnSlice, sliceWorker]
    "example : successful ((Zig.Sched.run Review.dispatch 10 (fun _ => 0) (Review.spawnSlice ⟨⟨some 0, 0⟩, 1⟩) Review.mem0).map fun (v, _) => v) = some () := by native_decide"
  for (mode, name) in #[(FloatSemantics.ieee, "floatIeee"), (.compilerRt, "floatCompilerRt")] do
    let expected : Nat := match mode with | .ieee => 512 | .compilerRt => 0
    writeCase directory name #[floatConversion]
      ("example : failedWith (Review.floatConversion (Zig.Float.ofBits (18446744073709551616 : BitVec 80))) Zig.Error.unspecified = true := by native_decide\n" ++
        s!"example : successful ((Review.floatConversion (Zig.Float.ofBits (301945530370514795626496 : BitVec 80))).map fun x => x.bits.toNat) = some {expected} := by native_decide") mode
  writeCase directory "legacyUnionTag" #[legacyUnion]
    "example : successful ((Review.legacyUnion 42).map BitVec.toNat) = some 42 := by native_decide"
  writeCase directory "escapingSafetyCheck" #[escapingSafetyCheck]
    "example : failedWith (Review.escapingSafetyCheck 2 1 true) Zig.Error.panic = true := by native_decide\nexample : successful ((Review.escapingSafetyCheck 1 2 true).map BitVec.toNat) = some 7 := by native_decide"
  writeCase directory "derivedInstanceNames" #[identityFile "foo", identityFile "instInhabitedFooLocals",
    structMembers, identityFile "instInhabitedS", identityFile "instReprS", identityFile "instDecidableEqS",
    packedInstanceName, identityFile "instEncP", identityFile "instPackedP"]
    "example : successful ((Review.instInhabitedFooLocals_air2lean1 8).map BitVec.toNat) = some 8 := by native_decide\nexample : successful ((Review.instInhabitedS_air2lean1 9).map BitVec.toNat) = some 9 := by native_decide"
  writeCase directory "binderTypeNames" #[structTypeShadow, localTypeShadow]
    "example : successful ((Review.structTypeShadow { BitVec_air2lean1 := 1, next := 2, T_air2lean1 := 3, tail := { value := 4 } }).map BitVec.toNat) = some 4 := by native_decide\nexample : successful ((Review.localTypeShadow 5).map BitVec.toNat) = some 5 := by native_decide"
  writeCase directory "classNames" #[identityFile "Repr", identityFile "Inhabited", identityFile "DecidableEq"]
    "example : successful ((Review.Repr_air2lean1 6).map BitVec.toNat) = some 6 := by native_decide"
  writeCase directory "underscoreName" #[identityFile "_"]
    "example : successful ((Review.«_» 7).map BitVec.toNat) = some 7 := by native_decide"
  writeCase directory "ctorIndexNames" #[ctorIndexName]
    "example : successful ((Review.ctorIndexName Review.CtorNames.ctorIdx_air2lean1).map BitVec.toNat) = some 0 := by native_decide"
  writeCase directory "generatedBinderTypeNames" #[enumBinderType, parameterBinderType, unionBinderType]
    "example : successful ((Review.enumBinderType Review.v_air2lean1.b).map BitVec.toNat) = some 1 := by native_decide\nexample : successful ((Review.parameterBinderType { value := 12 }).map fun x => x.value.toNat) = some 12 := by native_decide\nexample : successful ((Review.unionBinderType (Review.g_air2lean1.a 9)).map BitVec.toNat) = some 9 := by native_decide\nexample : successful ((Review.g_air2lean1.get_a (Review.g_air2lean1.modify_a (fun x => x + 1) (Review.g_air2lean1.a 9))).map BitVec.toNat) = some 10 := by native_decide"
  writeCase directory "indexedBinderTypeNames" #[instructionBinderType "i1" true,
    instructionBinderType "_i1" false, blockBinderType]
    "example : successful ((Review.instructionBinderType 13).map fun x => x.value.toNat) = some 13 := by native_decide\nexample : successful ((Review.unusedBinderType 14).map fun x => x.value.toNat) = some 14 := by native_decide\nexample : successful ((Review.blockBinderType 15).map fun x => x.value.toNat) = some 15 := by native_decide"
  writeCase directory "generatedBinderFunctionNames" #[identityFile "p0", functionBinderCall]
    "example : successful ((Review.functionBinderCall 16).map BitVec.toNat) = some 16 := by native_decide\nexample : successful ((Review.p0_air2lean1 17).map BitVec.toNat) = some 17 := by native_decide"
  let keywords := #["matches", "continue", "break", "unless", "panic!", "unreachable!",
    "assert!", "debug_assert!", "termination_by?", "max_prec", "eval_prec", "eval_prio",
    "s!", "f!", "println!", "show_term", "by?"]
  writeCase directory "reservedKeywordNames"
    (keywords.flatMap fun keyword => #[identityFile keyword, keywordField keyword])
    (String.intercalate "\n" (keywords.toList.flatMap fun keyword =>
      [s!"example : successful ((Review.{mangleName "" keyword} 18).map BitVec.toNat) = some 18 := by native_decide",
       s!"example : successful ((Review.{mangleName "" s!"keywordField_{keyword}"} ⟨19⟩).map BitVec.toNat) = some 19 := by native_decide"]))
  IO.println "emitter regression sources written"
