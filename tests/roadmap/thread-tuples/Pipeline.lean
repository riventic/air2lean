import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def lit (ty : Nat) (text : String) : Json := obj [("ty", num ty), ("val", .str text)]
private def undef (ty : Nat) : Json := obj [("ty", num ty), ("undef", .bool true)]
private def nominal (name : String) : Json := obj [("k", .str "struct"), ("name", .str name),
  ("layout", .str "auto"), ("fields", .arr #[]), ("abi_size", num 0), ("abi_align", num 1)]
private def node (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def u8 := obj [("k", .str "int"), ("signed", .bool false), ("bits", num 8),
  ("abi_size", num 1), ("abi_align", num 1)]
private def u16 := obj [("k", .str "int"), ("signed", .bool false), ("bits", num 16),
  ("abi_size", num 2), ("abi_align", num 2)]
private def voidTy := obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)]
private def nrTy := obj [("k", .str "noreturn")]
private def tuple (fields : Array Nat) :=
  obj [("k", .str "tuple"), ("fields", .arr (fields.map fun ty => obj [("ty", num ty)]))]
private def file (name : String) (types : Array Json) (params : Array Nat) (ret : Nat)
    (body : Array Json) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr types), ("params", toJson params), ("ret", num ret), ("body", .arr body)]
private def parse (j : Json) : IO Func := do
  match (do let f ← normalize (← Raw.parseFunc j); check f; pure f : Except String Func) with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def checkedProgram (files : Array Json) : IO (Array Func) := do
  let fs ← files.mapM parse
  match checkProgram fs with
  | .ok _ => pure fs
  | .error e => throw (IO.userError e)

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def requireError (result : Except String Unit) (expected : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"expected rejection: {expected}")
  | .error error => require (error == expected) s!"expected {expected}, got {error}"

/-- A spawning function. Only `Thread.spawn`'s `SpawnConfig` may be `undefined` (the model does
not read it); an `Io.Group` call's group pointer and `io` are runtime parameters. -/
private def spawner (callee : String) (fields : Array Nat) (values : Array Json) : Json :=
  let group := callee != "Thread.spawn"
  let lead : Array Json := if group then
      #[node 0 "arg" 10 #[] [("param", num 0)], node 1 "arg" 11 #[] [("param", num 1)]]
    else #[]
  let k := lead.size
  file "spawn" #[u8, u16, tuple fields, voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread"), ("fields", .arr #[])],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 5)],
    nominal "Thread.SpawnConfig", nominal "Io.Group",
    obj [("k", .str "ptr"), ("size", .str "one"), ("const", .bool false), ("child", num 9),
      ("abi_size", num 8), ("abi_align", num 8), ("ptr_align", num 1)],
    nominal "Io", obj [("k", .str "error_union"), ("error", num 6), ("payload", num 3)]]
    (if group then #[10, 11] else #[]) 3
    (lead ++ #[node k "aggregate_init" 2 values,
      node (k + 1) "call" (if callee == "Thread.spawn" then 7 else if callee == "Io.Group.concurrent" then 12 else 3)
        (if group then #[ref 0, ref 1, ref k] else #[undef 8, ref k])
        [("callee", obj [("func", .str callee), ("comptime_fn", .str "worker")])],
      node (k + 2) "ret" 4 #[lit 3 "{}"]])

private def worker (params : Array Nat) (retVoid : Bool := false) : Json :=
  file "worker" #[u8, u16, voidTy, nrTy] params (if retVoid then 2 else 0)
    ((params.mapIdx fun i ty => node i "arg" ty #[] [("param", num i)]) ++
      #[node params.size "ret" 3 #[if retVoid then lit 2 "{}" else lit 0 "7"]])

private def accepted (callee : String) (fields : Array Nat) (values : Array Json)
    (params : Array Nat) (retVoid : Bool := false) : IO (Array Func) := do
  checkedProgram #[spawner callee fields values, worker params retVoid]

private def rejected (_name callee : String) (fields : Array Nat) (values : Array Json)
    (params : Array Nat) (diagnostic : String) (retVoid : Bool := false) : IO Unit := do
  let fs ← #[spawner callee fields values, worker params retVoid].mapM parse
  requireError (checkProgram fs) diagnostic

private def pureSlices (sourceConst : Bool := true) : IO (Array Func) := do
  let slice := obj [("k", .str "ptr"), ("size", .str "slice"), ("const", .bool true),
    ("child", num 0), ("ptr_align", num 1), ("abi_size", num 16), ("abi_align", num 8)]
  let captureSlice := slice.setObjVal! "const" (.bool sourceConst)
  let source := file "slices" #[u8, captureSlice, tuple #[0, 1, 1], voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread"), ("fields", .arr #[])],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 5)],
    nominal "Thread.SpawnConfig"] #[1, 1] 3
    #[node 0 "arg" 1 #[] [("param", num 0)], node 1 "arg" 1 #[] [("param", num 1)],
      node 2 "aggregate_init" 2 #[lit 0 "7", ref 0, ref 1],
      node 3 "call" 7 #[undef 8, ref 2]
        [("callee", obj [("func", .str "Thread.spawn"), ("comptime_fn", .str "sliceWorker")])],
      node 4 "ret" 4 #[lit 3 "{}"]]
  let target := file "sliceWorker" #[u8, slice, nrTy] #[0, 1, 1] 0
    #[node 0 "arg" 0 #[] [("param", num 0)], node 1 "arg" 1 #[] [("param", num 1)],
      node 2 "arg" 1 #[] [("param", num 2)], node 3 "ret" 2 #[ref 0]]
  checkedProgram #[source, target]

private def alignedSlices : IO (Array Func) := do
  let u64 := obj [("k", .str "int"), ("signed", .bool false), ("bits", num 64),
    ("abi_size", num 8), ("abi_align", num 8)]
  let slice := fun align => obj [("k", .str "ptr"), ("size", .str "slice"),
    ("const", .bool true), ("child", num 0), ("ptr_align", num align),
    ("abi_size", num 16), ("abi_align", num 8)]
  let source := fun name align => file name #[u64, slice align, tuple #[1], voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread"), ("fields", .arr #[])],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 5)],
    nominal "Thread.SpawnConfig"] #[1] 3
    #[node 0 "arg" 1 #[] [("param", num 0)], node 1 "aggregate_init" 2 #[ref 0],
      node 2 "call" 7 #[undef 8, ref 1]
        [("callee", obj [("func", .str "Thread.spawn"), ("comptime_fn", .str "alignedWorker")])],
      node 3 "ret" 4 #[lit 3 "{}"]]
  let target := file "alignedWorker" #[u64, slice 1, voidTy, nrTy] #[1] 2
    #[node 0 "arg" 1 #[] [("param", num 0)], node 1 "ret" 3 #[lit 2 "{}"]]
  checkedProgram #[source "strongCapture" 8, source "weakCapture" 1, target]

private def pointerSignature (sourceConst targetConst : Bool) (sourceAlign targetAlign : Nat)
    (expected : Bool) : IO Unit := do
  let ptr := fun child constant align => obj [("k", .str "ptr"), ("size", .str "one"),
    ("const", .bool constant), ("child", num child), ("ptr_align", num align),
    ("abi_size", num 8), ("abi_align", num 8)]
  let source := file "pointerCapture" #[u8, ptr 0 sourceConst sourceAlign, tuple #[1], voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread"), ("fields", .arr #[])],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 5)],
    nominal "Thread.SpawnConfig"] #[1] 3
    #[node 0 "arg" 1 #[] [("param", num 0)], node 1 "aggregate_init" 2 #[ref 0],
      node 2 "call" 7 #[undef 8, ref 1]
        [("callee", obj [("func", .str "Thread.spawn"), ("comptime_fn", .str "worker")])],
      node 3 "ret" 4 #[lit 3 "{}"]]
  -- The same pointee lives at a different local type ID in the worker.
  let target := file "worker" #[u16, voidTy, nrTy, u8, ptr 3 targetConst targetAlign] #[4] 1
    #[node 0 "arg" 4 #[] [("param", num 0)], node 1 "ret" 2 #[lit 1 "{}"]]
  let fs ← #[source, target].mapM parse
  if expected then
    match checkProgram fs with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"valid pointer capture rejected: {error}")
  else
    requireError (checkProgram fs)
      "pointerCapture: Thread.spawn argument 0 does not match worker 'worker' parameter 0; capture the exact runtime parameter type with an explicit cast"

private def nestedTuple : IO (Array Func) := do
  let source := file "nestedTuple" #[u8, u16, tuple #[0, 1], tuple #[2, 0], voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread"), ("fields", .arr #[])],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 7), ("payload", num 6)],
    nominal "Thread.SpawnConfig"] #[2, 0] 4
    #[node 0 "arg" 2 #[] [("param", num 0)], node 1 "arg" 0 #[] [("param", num 1)],
      node 2 "aggregate_init" 3 #[ref 0, ref 1],
      node 3 "call" 8 #[undef 9, ref 2]
        [("callee", obj [("func", .str "Thread.spawn"), ("comptime_fn", .str "worker")])],
      node 4 "ret" 5 #[lit 4 "{}"]]
  let target := file "worker" #[u8, u16, tuple #[0, 1], nrTy] #[2, 0] 0
    #[node 0 "arg" 2 #[] [("param", num 0)], node 1 "arg" 0 #[] [("param", num 1)],
      node 2 "ret" 3 #[ref 1]]
  checkedProgram #[source, target]

private def nestedPointerSignature : IO Unit := do
  let ptr := fun child constant => obj [("k", .str "ptr"), ("size", .str "one"),
    ("const", .bool constant), ("child", num child), ("ptr_align", num 4),
    ("abi_size", num 8), ("abi_align", num 8)]
  let source ← parse (file "nestedSource" #[u8, ptr 0 false, ptr 1 false, voidTy, nrTy] #[2] 3
    #[node 0 "arg" 2 #[] [("param", num 0)], node 1 "ret" 4 #[lit 3 "{}"]])
  let target ← parse (file "nestedTarget" #[u16, voidTy, nrTy, u8, ptr 3 true, ptr 4 false] #[5] 1
    #[node 0 "arg" 5 #[] [("param", num 0)], node 1 "ret" 2 #[lit 1 "{}"]])
  require (!(sameSpawnTy source target 2 5)) "implicitly weakened nested pointer constness"

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Pipeline.lean OUTPUT")
  for callee in #["Thread.spawn", "Io.Group.async", "Io.Group.concurrent"] do
    let group := callee != "Thread.spawn"
    let _ ← accepted callee #[] #[] #[] group
    let _ ← accepted callee #[0] #[lit 0 "1"] #[0] group
    let _ ← accepted callee #[0, 1, 0, 1] #[lit 0 "1", lit 1 "2", lit 0 "3", lit 1 "4"] #[0, 1, 0, 1] group
    let diagnosticName := if group then "Io.Group.async" else "Thread.spawn"
    rejected "missing parameter" callee #[] #[] #[0]
      s!"spawn: {diagnosticName}'s args tuple has 0 fields, but worker 'worker' has 1 runtime parameters" group
    rejected "extra parameter" callee #[0, 0] #[lit 0 "1", lit 0 "2"] #[0]
      s!"spawn: {diagnosticName}'s args tuple has 2 fields, but worker 'worker' has 1 runtime parameters" group
    rejected "wrong middle field width" callee #[0, 1, 0] #[lit 0 "1", lit 1 "2", lit 0 "3"] #[0, 0, 0]
      s!"spawn: {diagnosticName} argument 1 does not match worker 'worker' parameter 1; capture the exact runtime parameter type with an explicit cast" group
  let noTuple := file "noTuple" #[u8, u16, tuple #[], voidTy, nrTy,
    obj [("k", .str "struct"), ("name", .str "Thread"), ("fields", .arr #[])],
    obj [("k", .str "error_set"), ("errors", .arr #[.str "ThreadQuotaExceeded"])],
    obj [("k", .str "error_union"), ("error", num 6), ("payload", num 5)],
    nominal "Thread.SpawnConfig"] #[] 3
    #[node 0 "call" 7 #[undef 8, lit 0 "7"]
      [("callee", obj [("func", .str "Thread.spawn"), ("comptime_fn", .str "worker")])],
      node 1 "ret" 4 #[lit 3 "{}"]]
  let nonTuple ← #[noTuple, worker #[]].mapM parse
  requireError (checkProgram nonTuple) "noTuple: Thread.spawn's args argument is not a tuple"
  let wrongResult := file "worker" #[u8, u16, voidTy, nrTy] #[] 1
    #[node 0 "ret" 3 #[lit 1 "7"]]
  let invalidResult ← #[spawner "Thread.spawn" #[] #[], wrongResult].mapM parse
  requireError (checkProgram invalidResult)
    "spawn: Thread.spawn worker 'worker' has an unsupported result; supported workers return void or noreturn, and Thread.spawn also accepts u8; error-return handling is outside the model"
  rejected "invalid group result" "Io.Group.async" #[0] #[lit 0 "1"] #[0]
    "spawn: Io.Group.async worker 'worker' has an unsupported result; supported workers return void or noreturn, and Thread.spawn also accepts u8; error-return handling is outside the model"
  nestedPointerSignature
  pointerSignature false false 4 4 true
  pointerSignature false true 4 1 true
  pointerSignature true false 4 4 false
  pointerSignature false false 1 4 false
  let fs ← accepted "Thread.spawn" #[0, 0, 0] #[lit 0 "1", lit 0 "2", lit 0 "9"] #[0, 0, 0]
  let orderWorker := file "worker" #[u8, nrTy] #[0, 0, 0] 0
    #[node 0 "arg" 0 #[] [("param", num 0)], node 1 "arg" 0 #[] [("param", num 1)],
      node 2 "arg" 0 #[] [("param", num 2)], node 3 "sub_safe" 0 #[ref 1, ref 2],
      node 4 "ret" 1 #[ref 3]]
  let fs := fs.set! 1 (← parse orderWorker)
  -- A declaration matching a dispatcher local must be renamed by the shared
  -- allocator, or the local would shadow an unqualified generated call.
  let some capturedWorker := fs[1]?
    | throw (IO.userError "ordered spawn fixture is missing its worker")
  let fs := fs.push { capturedWorker with name := "capture0" }
  let generated := emit fs "TuplePipeline" ""
  require ((generated.splitOn "def capture0_air2lean1").length == 2)
    "dispatcher capture local was not reserved by the declaration allocator"
  require ((generated.splitOn "worker capture0 capture1 capture2").length == 2) "three-field dispatch lost source order"
  let single ← accepted "Thread.spawn" #[0] #[lit 0 "1"] #[0]
  let singleSource := emit single "TupleSingle" ""
  require ((singleSource.splitOn "| worker (a : BitVec 8)").length == 2)
    "legacy one-field target lost its scalar constructor"
  require ((singleSource.splitOn "worker a)").length == 2)
    "legacy one-field dispatcher changed argument shape"
  let nested ← nestedTuple
  let nestedSource := emit nested "TupleNested" ""
  let slices ← pureSlices
  let sliceSource := emit slices "TupleSlices" ""
  require ((sliceSource.splitOn "Zig.readSlice").length == 3) "dispatcher did not adapt both pure slice arguments"
  let mutableSlices ← pureSlices false
  let mutableSliceSource := emit mutableSlices "TupleMutableSlices" ""
  require ((mutableSliceSource.splitOn "Zig.readSlice").length == 3)
    "mutable captures were not converted for the const pure worker contract"
  let aligned ← alignedSlices
  let alignedSource := emit aligned "TupleAlignedSlices" ""
  require ((alignedSource.splitOn "Zig.readSlice (BitVec 64) 1 a").length == 2)
    "dispatcher used first capture alignment instead of worker alignment"
  -- Per-argument ownership classes: values carry none; pointers and slices must be granted.
  require ((sliceSource.splitOn "| .sliceWorker (_, capture1, capture2) => [.value, .slice capture1, .slice capture2]").length == 2)
    "slice captures were not classified for ownership transfer"
  require ((singleSource.splitOn "Tgt.captures").length == 1)
    "legacy one-field program gained a capture classification"
  let classes := emitTgtCaptures #[("zero", #[]), ("one", #[.ptr]), ("val", #[.value]),
    ("mix", #[.other, .slice, .value])]
  for line in ["  | .zero _ => []", "  | .one a => [.ptr a]", "  | .val _ => [.value]",
      "  | .mix (_, capture1, _) => [.other, .slice capture1, .value]"] do
    require ((classes.splitOn line).length == 2) s!"capture classification lost: {line}"
  let types : Array Ty := #[.int false 8, .ptr "one" false 0, .struct "Plain" "auto" #[("x", 0)],
    .struct "Holder" "auto" #[("p", 1)], .optional 1, .allocator, .ptr "slice" true 0,
    .tuple #[0, 2], .array 4 1 false, .io]
  for (id, expected) in [(0, CaptureClass.value), (1, .ptr), (2, .value), (3, .other), (4, .other),
      (5, .other), (6, .slice), (7, .value), (8, .other), (9, .other)] do
    require (captureClass types id == expected) s!"type {id} has the wrong capture class"
  let proof := "\nexample (a b c : BitVec 8) : TuplePipeline.dispatch (.worker (a, b, c)) = discard (Zig.ConcM.liftMem (StateT.lift (TuplePipeline.worker a b c))) := by rfl\n" ++
    "example {γ : Type} (P : Zig.Conc.Proto TuplePipeline.Tgt γ) (a b c : BitVec 8) (g : γ) : TuplePipeline.Tgt.spawnInit P (.worker (a, b, c)) g = P.init (.worker (a, b, c)) g := by rfl\n" ++
    "example (a b c : BitVec 8) : TuplePipeline.Tgt.captures (.worker (a, b, c)) = [.value, .value, .value] := rfl\n"
  IO.FS.writeFile output (generated ++ proof)
  IO.FS.writeFile (output ++ ".nested.lean") (nestedSource ++
    "\nexample (first : BitVec 8 × BitVec 16) (second : BitVec 8) : TupleNested.dispatch (.worker (first, second)) = discard (Zig.ConcM.liftMem (StateT.lift (TupleNested.worker first second))) := by rfl\n" ++
    "example (first : BitVec 8 × BitVec 16) (second : BitVec 8) : TupleNested.Tgt.captures (.worker (first, second)) = [.value, .value] := rfl\n")
  IO.FS.writeFile (output ++ ".slices.lean") (sliceSource ++
    "\nexample (a : BitVec 8) (s t : Zig.Slice) : TupleSlices.Tgt.captures (.sliceWorker (a, s, t)) = [.value, .slice s, .slice t] := rfl\n")
  IO.FS.writeFile (output ++ ".single.lean") (singleSource ++
    "\nexample (a : BitVec 8) : TupleSingle.dispatch (.worker a) = discard (Zig.ConcM.liftMem (StateT.lift (TupleSingle.worker a))) := by rfl\n")
  IO.FS.writeFile (output ++ ".mutable-slices.lean") mutableSliceSource
  IO.FS.writeFile (output ++ ".aligned-slices.lean") (alignedSource ++
    "\nexample (a : Zig.Slice) : TupleAlignedSlices.dispatch (.alignedWorker a) = discard (Zig.ConcM.liftMem (do let items ← Zig.readSlice (BitVec 64) 1 a; StateT.lift (TupleAlignedSlices.alignedWorker items))) := by rfl\n" ++
    "private def weakRead : Zig.ConcM TupleAlignedSlices.Tgt Unit := do\n  let p ← Zig.ConcM.liftMem (Zig.alloc .heap 9 1)\n  let q := p.add 1\n  Zig.ConcM.liftMem (Zig.store 1 q (42#64))\n  let .ok child ← Zig.ConcM.sync (.spawn (.alignedWorker { ptr := q, len := 1 })) | pure ()\n  let _ ← Zig.ConcM.sync (.join child)\n  pure ()\ndef main : IO Unit := do\n  unless ((Zig.Sched.run ⟨.any, .available⟩ TupleAlignedSlices.dispatch 100 (fun _ => 0) weakRead {}).run matches some (.ok ((), _))) do\n    throw (IO.userError \"valid unaligned slice rejected by stronger first capture\")\n")
  IO.println "thread tuple parser/checker/emitter regressions passed"
