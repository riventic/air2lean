import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
import Air2Lean.Air.Anon

/-! Focused regressions for accepted AIR semantics and fail-closed parsing.
Run with `lake env lean --run tests/review/Parser.lean OUTPUT_DIR`. The driver writes
generated semantic regressions for separate, serialized compilation; it never starts a compiler. -/

open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (id : Nat) : Json := obj [("inst", num id)]
private def lit (ty : Nat) (v : String) : Json := obj [("ty", num ty), ("val", .str v)]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def intTy (bits : Nat) (signed : Bool := false) : Json :=
  obj [("k", .str "int"), ("signed", .bool signed), ("bits", num bits),
    ("abi_size", num (Zig.intSize bits)), ("abi_align", num (Zig.intAlign bits))]
private def ptrTy (size : String) (child : Nat) (const_ : Bool := false) : Json :=
  obj [("k", .str "ptr"), ("size", .str size), ("const", .bool const_), ("child", num child),
    ("ptr_align", num 1), ("abi_size", num (if size == "slice" then 16 else 8)), ("abi_align", num 8)]
private def boolTy : Json := obj [("k", .str "bool")]
private def voidTy : Json := obj [("k", .str "void")]
private def nrTy : Json := obj [("k", .str "noreturn")]
private def file (name : String) (types : Array Json) (params : Array Nat) (ret : Nat)
    (body : Array Json) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("name", .str name),
    ("types", .arr types), ("params", toJson params), ("ret", num ret), ("body", .arr body)]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def accept (j : Json) : IO Func :=
  match process j with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def reject (j : Json) (what : String) : IO Unit :=
  require (process j |>.toOption.isNone) s!"accepted {what}"
private def writeGenerated (directory : System.FilePath) (name : String) (f : Func)
    (assertion : String) : IO Unit := do
  IO.FS.writeFile (directory / (name ++ ".lean"))
    (emit #[f] "Review" "" ++ "\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption\n" ++ assertion ++ "\n")

private def packedNegative : Json :=
  file "packedNeg" #[intTy 8 true, obj [("k", .str "struct"), ("name", .str "P"),
    ("layout", .str "packed"), ("fields", .arr #[obj [("name", .str "x"), ("ty", num 0)]])], nrTy]
    #[] 1 #[inst 10 "ret" 2 #[lit 1 ".{ .x = -1 }"]]
private def sliceAlias : Json :=
  file "sliceAlias" #[intTy 8, intTy 64, ptrTy "slice" 0, ptrTy "one" 0, voidTy, nrTy]
    #[2, 3] 0 #[inst 10 "arg" 2 #[] [("param", num 0)], inst 20 "arg" 3 #[] [("param", num 1)],
      inst 30 "slice_elem_ptr" 3 #[ref 10, lit 1 "0"],
      inst 40 "store" 4 #[ref 20, lit 0 "7"], inst 50 "load" 0 #[ref 30],
      inst 60 "ret" 5 #[ref 50]]
private def valueBlock : Json :=
  file "valueBlock" #[intTy 8, boolTy, voidTy, nrTy] #[0] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "cmp_lte" 1 #[lit 0 "0", ref 10],
      inst 0 "block" 0 #[] [("body", .arr #[inst 40 "cond_br" 3 #[ref 20]
        [("then", .arr #[inst 50 "br" 3 #[lit 0 "42"] [("target", num 0)]]),
         ("else", .arr #[inst 60 "unreach" 3])]])], inst 70 "ret" 3 #[ref 0]]

private def enumNames : Json :=
  file "enumName" #[intTy 8, obj [("k", .str "enum"), ("name", .str "E"), ("tag", num 0),
    ("exhaustive", .bool true), ("fields", .arr #[obj [("name", .str "literal__anon_99"),
      ("value", .str "0")], obj [("name", .str "other"), ("value", .str "1")]]),
    ("abi_size", num 1), ("abi_align", num 1)],
    ptrTy "slice" 0 true, nrTy] #[1] 2 #[inst 5 "arg" 1 #[] [("param", num 0)],
      inst 10 "tag_name" 2 #[ref 5], inst 20 "ret" 3 #[ref 10]]

private def vectorFile (bits : Nat) (lane : Bool) : Json :=
  let vec := obj [("k", .str "vector"), ("len", num 4), ("child", num 0),
    ("abi_size", num (Zig.vecLayout 4 (Zig.intSize bits))),
    ("abi_align", num (Zig.vecLayout 4 (Zig.intSize bits)))]
  file "vectorLoad" #[intTy bits, vec, ptrTy "one" 1, ptrTy "one" 0, intTy 64, nrTy]
    #[2] (if lane then 0 else 1) (if lane then
      #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "ptr_elem_ptr" 3 #[ref 0, lit 4 "1"],
        inst 2 "load" 0 #[ref 1], inst 3 "ret" 5 #[ref 2]]
    else #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "load" 1 #[ref 0],
      inst 2 "ret" 5 #[ref 1]])

private def opvFile (zero : Json) (sourceIndex : Nat) : Json :=
  file "opv" #[zero, intTy 32, nrTy] #[0, 1] 1
    #[inst 10 "arg" 1 #[] [("param", num sourceIndex)],
      inst 20 "add" 1 #[ref 10, lit 1 "1"], inst 30 "ret" 2 #[ref 20]]

private def asmFile (output input : String) : Json :=
  file "asmReg" #[intTy 32, nrTy] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "assembly" 0 #[]
      [("source", .str ""), ("volatile", .bool false), ("clobbers", .arr #[]),
       ("outputs", .arr #[obj [("constraint", .str output), ("name", .str "out")]]),
       ("inputs", .arr #[obj [("constraint", .str input), ("name", .str "in"), ("ref", ref 0)]])],
     inst 2 "ret" 1 #[ref 1]]

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Parser.lean OUTPUT_DIR")
  let directory : System.FilePath := output
  IO.FS.createDirAll directory
  writeGenerated directory "packedNegative" (← accept packedNegative)
    "example : successful (Review.packedNeg.map fun v => Zig.val true v.x) = some (-1) := by native_decide"
  writeGenerated directory "sliceAlias" (← accept sliceAlias)
    "example : successful ((((do let p ← Zig.allocStack 1 1; Zig.store 1 p (3 : BitVec 8); Review.sliceAlias ⟨p, 1⟩ p) : Zig.MemM (BitVec 8)).run {}).map fun (v, _) => v.toNat) = some 7 := by native_decide"
  writeGenerated directory "valueBlock" (← accept valueBlock)
    "example : successful ((Review.valueBlock 17).map BitVec.toNat) = some 42 := by native_decide"
  reject (file "badBool" #[boolTy, nrTy] #[] 0 #[inst 0 "ret" 1 #[lit 0 "garbage"]]) "bad bool"
  reject (file "badVoid" #[voidTy, nrTy] #[] 0 #[inst 0 "ret" 1 #[lit 0 "garbage"]]) "bad void"
  reject (file "missingRef" #[intTy 8, nrTy] #[0] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "ret" 1 #[ref 0]]) "absent raw ref"
  let nested := file "nested" #[intTy 8,
    obj [("k", .str "array"), ("len", num 1), ("child", num 0)], nrTy] #[0] 1
    #[inst 20 "arg" 0 #[] [("param", num 0)],
      inst 30 "ret" 2 #[obj [("ty", num 1), ("elems", .arr #[ref 20])]]]
  match process nested with
  | .ok _ => throw (IO.userError "accepted nested SSA ref in an aggregate constant")
  | .error e =>
    require ((e.splitOn "nested instruction ref 20").length > 1)
      s!"wrong nested-ref diagnostic: {e}"
  for maskId in #[1, 0] do
    let mask := file "maskRef" #[intTy 8,
      obj [("k", .str "vector"), ("len", num 1), ("child", num 0)], nrTy] #[0, 0, 1] 1
      #[inst 1 "arg" 0 #[] [("param", num 0)], inst 10 "arg" 0 #[] [("param", num 1)],
        inst 20 "arg" 1 #[] [("param", num 2)], inst 30 "shuffle_one" 1 #[ref 20]
          [("mask", .arr #[obj [("v", ref maskId)]])], inst 40 "ret" 2 #[ref 30]]
    match process mask with
    | .ok _ => throw (IO.userError s!"accepted SSA shuffle mask ref {maskId}")
    | .error e =>
      require ((e.splitOn "inside a shuffle mask").length > 1)
        s!"wrong shuffle-mask diagnostic: {e}"
  let global := (file "globalRef" #[intTy 8, nrTy] #[0] 0
    #[inst 20 "arg" 0 #[] [("param", num 0)], inst 30 "ret" 1 #[ref 20]]).setObjVal! "globals"
    (.arr #[obj [("ty", num 0), ("const", .bool true), ("init", ref 20)]])
  match process global with
  | .ok _ => throw (IO.userError "accepted SSA ref in a global initializer")
  | .error e =>
    require ((e.splitOn "inside a global initializer").length > 1)
      s!"wrong global-initializer diagnostic: {e}"
  reject (file "duplicate" #[intTy 8, nrTy] #[0] 0
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 10 "ret" 1 #[ref 10]]) "duplicate raw id"
  reject (file "badTarget" #[voidTy, nrTy] #[] 0
    #[inst 10 "block" 0, inst 20 "br" 1 #[lit 0 "{}"] [("target", num 10)]]) "non-enclosing target"
  reject (file "badRepeat" #[voidTy, nrTy] #[] 0
    #[inst 10 "block" 0 #[] [("body", .arr #[inst 20 "repeat" 1 #[] [("target", num 10)]])]])
    "repeat targeting block"
  reject (file "unknownPanic" #[intTy 8, nrTy] #[] 0 #[inst 0 "call" 1 #[]
    [("callee", obj [("func", .str "user.call"), ("noreturn", .bool true)])]]) "user noreturn"
  require (panicErrorFor? "debug.FullPanic((function 'defaultPanic')).outOfBounds" == some ".outOfBounds")
    "known panic handler rejected"
  require (panicErrorFor? "debug.FullPanic((function 'defaultPanic')).shiftRhsTooBig" == some ".overflow")
    "shift-count panic handler not mapped like shlOverflow/shrOverflow"
  require (panicErrorFor? "debug.defaultPanic" == some ".panic")
    "exact standard default panic handler rejected"
  let defaultPanic ← accept (file "defaultPanic" #[intTy 8, nrTy] #[] 0
    #[inst 0 "call" 1 #[]
      [("callee", obj [("func", .str "debug.defaultPanic"), ("noreturn", .bool true)])]])
  writeGenerated directory "defaultPanic" defaultPanic
    "example : Review.defaultPanic = some (.error .panic) := by rfl"
  for name in #["my.defaultPanic", "debug.defaultPanic__anon_1", "debug.defaultPanic.call"] do
    require ((panicErrorFor? name).isNone) s!"accepted nearby foreign panic handler: {name}"
    reject (file "foreignDefaultPanic" #[intTy 8, nrTy] #[] 0
      #[inst 0 "call" 1 #[]
        [("callee", obj [("func", .str name), ("noreturn", .bool true)])]])
      "foreign defaultPanic noreturn handler"
  let returningDefaultPanic ← accept (file "returningDefaultPanic" #[intTy 8, nrTy] #[] 0
    #[inst 0 "call" 0 #[] [("callee", obj [("func", .str "debug.defaultPanic")])],
      inst 1 "ret" 1 #[ref 0]])
  require ((checkProgram #[returningDefaultPanic]).toOption.isNone)
    "default panic name bypassed the noreturn-only model boundary"
  let bitPtr := ((ptrTy "one" 0).setObjVal! "host_size" (num 1)).setObjVal! "vector_index" .null
  reject (file "missingOffset" #[intTy 4, bitPtr, nrTy] #[1] 0
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "load" 0 #[ref 0],
      inst 2 "ret" 2 #[ref 1]]) "bit pointer without offset"
  let _ ← accept (file "validOffset" #[intTy 4, bitPtr.setObjVal! "bit_offset" (num 4), nrTy]
    #[1] 0 #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "load" 0 #[ref 0],
      inst 2 "ret" 2 #[ref 1]])
  reject (file "badOffset" #[intTy 4, bitPtr.setObjVal! "bit_offset" (num 8), nrTy]
    #[1] 0 #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "load" 0 #[ref 0],
      inst 2 "ret" 2 #[ref 1]]) "bit pointer crossing host boundary"
  reject (packedNegative.setObjVal! "target_endian" (.str "big")) "big-endian target"
  let _ ← accept (packedNegative.setObjVal! "target_endian" (.str "little"))
  let renamed := Anon.renumberAll #[enumNames.compress]
  let preserved ← accept (← match Json.parse renamed[0]! with
    | .ok j => pure j | .error e => throw (IO.userError e))
  writeGenerated directory "enumNames" preserved
    "example : successful ((Review.E.tagName Review.E.literal__anon_99).map (·.len.toNat)) = some 16 := by native_decide"
  let identities := obj [("name", .str "generic__anon_99"), ("types", .arr #[]),
    ("source", .str "generic__anon_99"), ("body", .arr #[obj [("callee", obj [("func", .str "generic__anon_99")])]])]
  let ren := (Anon.renumberAll #[identities.compress])[0]!
  let j ← match Json.parse ren with | .ok j => pure j | .error e => throw (IO.userError e)
  require ((j.getObjValAs? String "name").toOption == some "generic__anon_1") "function identity not renamed"
  require ((j.getObjValAs? String "source").toOption == some "generic__anon_99") "asm text renamed"
  let inputs := #[identities.compress, enumNames.compress, "invalid JSON"]
  let individual := ["__anon_", "__struct_", "__enum_", "__union_", "__opaque_"].foldl
    (fun texts marker => Anon.renumberAnon texts marker) inputs
  require (Anon.renumberAll inputs == individual) "cached anonymous renumbering changed pass ordering"
  require ((Anon.renumberAll inputs)[2]! == "invalid JSON") "malformed JSON was rewritten"
  for b in #[9, 24, 40, 80] do
    reject (vectorFile b false) s!"padded vector({b}) load"
    reject (vectorFile b true) s!"padded vector({b}) lane load"
  let _ ← accept (vectorFile 32 false)
  let _ ← accept (vectorFile 32 true)
  let floatVec := (vectorFile 80 false).setObjVal! "types" (.arr
    #[obj [("k", .str "float"), ("bits", num 80), ("abi_size", num 16), ("abi_align", num 16)],
      obj [("k", .str "vector"), ("len", num 4), ("child", num 0),
        ("abi_size", num 64), ("abi_align", num 64)],
      ptrTy "one" 1, ptrTy "one" 0, intTy 64, nrTy])
  reject floatVec "f80 vector memory"
  let _ ← accept (file "pureVector" #[intTy 9,
    obj [("k", .str "vector"), ("len", num 4), ("child", num 0)], nrTy] #[1] 1
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "ret" 2 #[ref 0]])
  writeGenerated directory "opvVoid" (← accept (opvFile voidTy 1))
    "example : successful ((Review.opv () 10).map BitVec.toNat) = some 11 := by native_decide"
  let opvZero ← accept (opvFile (intTy 0) 3)
  writeGenerated directory "opvZero" opvZero
    "example : successful ((Review.opv 0 10).map BitVec.toNat) = some 11 := by native_decide"
  require (isRegisterConstraint "=&{edx}" && isRegisterConstraint "=&r") "early-clobber output rejected"
  let _ ← accept (asmFile "=&{edx}" "r")
  reject (asmFile "=r" "=&r") "output constraint on asm input"
  -- Type-graph validation must precede recursive packed width and memory analysis.
  let cycPacked := obj [("k", .str "struct"), ("name", .str "Cycle"),
    ("layout", .str "packed"), ("fields", .arr #[obj [("name", .str "self"), ("ty", num 0)]])]
  let undef (ty : Nat) := obj [("ty", num ty), ("undef", .bool true)]
  for t in #[cycPacked, obj [("k", .str "optional"), ("child", num 0)],
      obj [("k", .str "array"), ("len", num 1), ("child", num 0)]] do
    reject (file "cycle" #[t, nrTy] #[] 0 #[inst 0 "ret" 1 #[undef 0]]) "cyclic value type"
  let node := obj [("k", .str "struct"), ("name", .str "Node"), ("layout", .str "auto"),
    ("fields", .arr #[obj [("name", .str "next"), ("ty", num 1)]])]
  let _ ← accept (file "recursivePointer" #[node, ptrTy "one" 0, nrTy] #[1] 1
    #[inst 0 "arg" 1 #[] [("param", num 0)], inst 1 "ret" 2 #[ref 0]])
  reject (file "selfUse" #[intTy 8, nrTy] #[] 0
    #[inst 10 "add" 0 #[ref 10, lit 0 "1"], inst 20 "ret" 1 #[ref 10]]) "self SSA use"
  reject (file "forwardUse" #[intTy 8, nrTy] #[] 0
    #[inst 10 "add" 0 #[ref 20, lit 0 "1"], inst 20 "add" 0 #[lit 0 "1", lit 0 "2"],
      inst 30 "ret" 1 #[ref 10]]) "forward SSA use"
  let branched (sibling : Bool) := file "branchScope" #[boolTy, intTy 8, nrTy] #[0] 1
    #[inst 10 "arg" 0 #[] [("param", num 0)], inst 20 "add" 1 #[lit 1 "1", lit 1 "2"],
      inst 30 "cond_br" 2 #[ref 10]
        [("then", .arr #[inst 40 "add" 1 #[ref 20, lit 1 "1"], inst 50 "ret" 2 #[ref 40]]),
         ("else", .arr #[inst 60 "ret" 2 #[ref (if sibling then 40 else 20)]])]]
  reject (branched true) "sibling SSA use"
  let _ ← accept (branched false)
  let agg (ty : Nat) (elems : Array Json) := obj [("ty", num ty), ("elems", .arr elems)]
  reject (file "scalarAggregate" #[intTy 8, nrTy] #[] 0
    #[inst 0 "ret" 1 #[agg 0 #[]]]) "aggregate constant on scalar"
  let arr := obj [("k", .str "array"), ("len", num 1), ("child", num 0)]
  for elems in #[#[], #[lit 0 "1", lit 0 "2"], #[lit 1 "1"]] do
    reject (file "badAggregate" #[intTy 8, intTy 16, arr, nrTy] #[] 2
      #[inst 0 "ret" 3 #[agg 2 elems]]) "aggregate count or child type"
  let _ ← accept (file "goodAggregate" #[intTy 8, arr, nrTy] #[] 1
    #[inst 0 "ret" 2 #[agg 1 #[lit 0 "7"]]])
  let optional := obj [("k", .str "optional"), ("child", num 0)]
  reject (file "badPayload" #[intTy 8, intTy 16, optional, nrTy] #[] 2
    #[inst 0 "ret" 3 #[obj [("ty", num 2), ("some", lit 1 "7")]]]) "optional child type"
  for marker in #[.bool false, .str "true", num 1, Json.null] do
    reject (file "badUndef" #[intTy 8, nrTy] #[] 0
      #[inst 0 "ret" 1 #[obj [("ty", num 0), ("undef", marker)]]]) "non-true undef marker"
    reject (file "badNull" #[intTy 8, optional, nrTy] #[] 1
      #[inst 0 "ret" 2 #[obj [("ty", num 1), ("null", marker)]]]) "non-true null marker"
    require ((Raw.parseMaskLane "mask" #[.int false 8]
      (obj [("u", marker)])).toOption.isNone) "accepted non-true shuffle marker"
  for k in #["noreturn", "volatile", "unsupported", "sentinel"] do
    require ((Raw.boolField (obj [(k, .str "false")]) k).toOption.isNone)
      s!"accepted malformed flag {k}"
    require ((Raw.boolField (obj [(k, .bool false)]) k).toOption == some false)
      s!"rejected literal false flag {k}"
  reject (file "badFlag" #[intTy 8, nrTy] #[] 0
    #[inst 0 "ret" 1 #[lit 0 "7"] [("unsupported", .str "false")]]) "malformed instruction flag"
  reject (file "ambiguousConstant" #[intTy 8, nrTy] #[] 0
    #[inst 0 "ret" 1 #[obj [("ty", num 0), ("undef", .bool true), ("val", .str "7")]]])
    "ambiguous constant form"
  for text in #[".{ .x = 12", ".{ .x = 12X"] do
    reject (packedNegative.setObjVal! "body" (.arr #[inst 10 "ret" 2 #[lit 1 text]]))
      "packed constant without closing brace"
  let vec (child : Nat) := obj [("k", .str "vector"), ("len", num 2), ("child", num child)]
  reject (file "pointerVector" #[intTy 8, ptrTy "one" 0, vec 1, nrTy] #[2] 2
    #[inst 0 "arg" 2 #[] [("param", num 0)], inst 1 "ret" 3 #[ref 0]]) "pointer vector"
  let castFile (source dest : Nat) := file "vectorCast" #[intTy 32, vec 0, intTy 64,
    obj [("k", .str "float"), ("bits", num 32)], vec 3, nrTy] #[source] dest
    #[inst 0 "arg" source #[] [("param", num 0)], inst 1 "bitcast" dest #[ref 0],
      inst 2 "ret" 5 #[ref 1]]
  reject (castFile 1 2) "vector-to-scalar bitcast"
  reject (castFile 2 1) "scalar-to-vector bitcast"
  reject (castFile 1 4) "integer-to-float vector bitcast"
  let _ ← accept (castFile 1 1)
  let tuple := obj [("k", .str "tuple"), ("fields", .arr #[obj [("ty", num 0)]])]
  let modelStruct (name : String) := obj [("k", .str "struct"), ("name", .str name),
    ("layout", .str "auto"), ("fields", .arr #[])]
  let spawnTypes := #[intTy 8, voidTy, tuple, nrTy, modelStruct "Thread.SpawnConfig",
    obj [("k", .str "error_set"), ("any", .bool true)], modelStruct "Thread",
    obj [("k", .str "error_union"), ("error", num 5), ("payload", num 6)],
    modelStruct "Io.Group", ptrTy "one" 8, modelStruct "Io"]
  -- Only `Thread.spawn`'s `SpawnConfig` may be `undefined`; the group and `io` are parameters.
  for (callee, args) in #[ ("Thread.spawn", #[undef 4, ref 2]),
      ("Io.Group.async", #[ref 0, ref 1, ref 2]) ] do
    let group := callee != "Thread.spawn"
    let result := if group then 1 else 7
    let spawn := file "spawnMissing" spawnTypes (if group then #[9, 10] else #[]) 1
      ((if group then #[inst 0 "arg" 9 #[] [("param", num 0)], inst 1 "arg" 10 #[] [("param", num 1)]]
        else #[]) ++
      #[inst 2 "aggregate_init" 2 #[lit 0 "7"], inst 3 "call" result args
        [("callee", obj [("func", .str callee), ("comptime_fn", .str "missingWorker")])],
        inst 4 "ret" 3 #[lit 1 "{}"]])
    let f ← accept spawn
    match checkProgram #[f] with
    | .ok _ => throw (IO.userError s!"accepted missing worker for {callee}")
    | .error e =>
      require ((e.splitOn "the spawned callee 'missingWorker' has no AIR file").length > 1)
        s!"wrong missing-worker diagnostic for {callee}: {e}"
    let workerFile (bits : Nat) := if callee == "Thread.spawn" then
      file "missingWorker" #[intTy bits, nrTy] #[0] 0
        #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "ret" 1 #[ref 0]]
      else file "missingWorker" #[intTy bits, voidTy, nrTy] #[0] 1
        #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "ret" 2 #[lit 1 "{}"]]
    let worker ← accept (workerFile 8)
    match checkProgram #[f, worker] with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"rejected present worker for {callee}: {e}")
    let incompatible ← accept (workerFile 16)
    match checkProgram #[f, incompatible] with
    | .ok _ => throw (IO.userError s!"accepted incompatible worker for {callee}")
    | .error e =>
      require ((e.splitOn s!"{callee} argument 0 does not match worker 'missingWorker' parameter 0").length > 1)
        s!"wrong incompatible-worker diagnostic for {callee}: {e}"
  IO.println "parser regressions passed"
