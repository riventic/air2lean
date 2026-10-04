import Air2Lean.Main

/-! Compiled evaluation checks for the direct API and strict parser, run by the root guard. -/
open Air2Lean

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def accepted (r : Except String Unit) : Bool := r.toOption.isSome
private def rejected (r : Except String Unit) (fragment : String) : Bool :=
  match r with
  | .error e => (e.splitOn fragment).length > 1
  | .ok _ => false

private def mkFunc (name : String) (types : Array Ty) (params : Array TyId) (ret : TyId)
    (body : Array Inst := #[]) (globals : Array Global := #[]) : Func := {
  zigVersion := "0.16.0"
  name
  types
  params
  ret
  body
  globals
  layouts := Array.replicate types.size {}
}

/-- Snapshot of the previous collector, used only on bounded fixtures to check that the
streamed closure keeps the same roots (including invalid IDs without diagnosing them). -/
private def previousUsedTypes (f : Func) : Std.HashSet TyId := Id.run do
  let rec constantTypes (v : Val) : Array TyId :=
    v.constTy?.toArray ++ match v with
      | .agg _ vs => vs.flatMap constantTypes
      | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => constantTypes v
      | .sliceConst _ p n => constantTypes p ++ constantTypes n
      | _ => #[]
  let insts := f.allInsts
  let values := insts.flatMap fun i => valueOperands i.op ++ ptrOperands i.op
  let roots := f.params ++ #[f.ret] ++ insts.map (·.ty) ++ values.flatMap constantTypes ++
    f.globals.map (·.ty) ++ f.globals.flatMap (fun g => g.init.toArray.flatMap constantTypes)
  let mut todo := roots.toList
  let mut seen : Std.HashSet TyId := {}
  while !todo.isEmpty do
    let id := todo.head!
    todo := todo.tail!
    if seen.contains id then continue
    seen := seen.insert id
    todo := ((f.types[id]?.map childTys).getD #[]).toList ++ todo
  return seen

private inductive PreviousDefinitionTask where
  | global (a b : Nat)
  | value (a b : Val)
  deriving Inhabited

/-- Pre-cleanup comparator snapshot for cache success/failure equivalence tests. -/
private def previousGlobalCached (a b : Func) (x y : Nat)
    (completed : Std.HashSet (Nat × Nat) := {}) : Option (Std.HashSet (Nat × Nat)) := Id.run do
  let mut todo := [PreviousDefinitionTask.global x y]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  while !todo.isEmpty do
    let task := todo.head!
    todo := todo.tail!
    match task with
    | .global i j =>
      if completed.contains (i, j) || seen.contains (i, j) then continue
      let some g := a.globals[i]? | return none
      let some h := b.globals[j]? | return none
      unless g.name == h.name && g.isConst == h.isConst && g.threadlocal == h.threadlocal &&
          g.isExtern == h.isExtern && compatibleType a b g.ty h.ty do return none
      seen := seen.insert (i, j)
      match g.init, h.init with
      | some v, some w => todo := .value v w :: todo
      | none, none => pure ()
      | _, _ => return none
    | .value v w =>
      let ty (i j : TyId) := compatibleType a b i j
      match v, w with
      | .int i v, .int j w | .enumTag i v, .enumTag j w =>
        unless v == w && ty i j do return none
      | .float i v, .float j w => unless v == w && ty i j do return none
      | .bool v, .bool w => unless v == w do return none
      | .void, .void => pure ()
      | .undef i, .undef j | .optNull i, .optNull j => unless ty i j do return none
      | .err i v, .err j w | .errUnionErr i v, .errUnionErr j w
      | .ptrOther i v, .ptrOther j w => unless v == w && ty i j do return none
      | .func v n s, .func w m t => unless v == w && n == m && s == t do return none
      | .optSome i v, .optSome j w | .errUnionOk i v, .errUnionOk j w =>
        unless ty i j do return none
        todo := .value v w :: todo
      | .unionVal i k v, .unionVal j l w =>
        unless k == l && ty i j do return none
        todo := .value v w :: todo
      | .agg i vs, .agg j ws =>
        unless vs.size == ws.size && ty i j do return none
        todo := (vs.zip ws |>.toList.map fun (v, w) => .value v w) ++ todo
      | .ptrConst i g off, .ptrConst j h off' =>
        unless off == off' && ty i j do return none
        todo := .global g h :: todo
      | .sliceConst i p n, .sliceConst j q m =>
        unless ty i j do return none
        todo := .value p q :: .value n m :: todo
      | _, _ => return none
  return some (Std.HashSet.fold (fun (cache : Std.HashSet (Nat × Nat)) pair => cache.insert pair) completed seen)


private def validationChecks : IO Unit := do
  let source := mkFunc "caller" #[.int false 32, .void] #[0] 0 #[
    { id := 0, ty := 0, op := .arg 0 },
    { id := 1, ty := 0, op := .call (.func "target" false) #[.inst 0] },
    { id := 2, ty := 1, op := .ret (.inst 1) }]
  let target := mkFunc "target" #[.void, .int false 32] #[1] 1 #[
    { id := 0, ty := 1, op := .arg 0 }, { id := 1, ty := 0, op := .ret (.inst 0) }]
  require (compatibleType source target 0 1) "reordered type IDs rejected"
  require (accepted (checkProgram #[source, target])) "cross-table direct call rejected"
  require (rejected (checkProgram #[source, { target with params := #[], body := #[] }]) "expected 0")
    "arity mutation accepted"
  require (rejected (checkProgram #[source, { target with types := #[.void, .int false 64] }])
    "incompatible result type") "result mutation accepted"
  let differentArg := { target with params := #[0], body := #[] }
  require (rejected (checkProgram #[source, differentArg]) "incompatible argument 0")
    "argument mutation accepted"
  require (rejected (checkProgram #[source, source]) "duplicate function") "duplicate name accepted"
  require (rejected (checkProgram #[{ target with ret := 99 }]) "unknown type id 99")
    "invalid direct signature accepted"
  require (rejected (checkProgram #[{ target with layouts := #[] }]) "layout table")
    "malformed parallel table accepted"
  require (rejected (checkProgram #[{ target with body := #[{ id := 0, ty := 0, op := .ret (.inst 77) }] }])
    "unknown instruction ref 77") "missing reference accepted"
  let nodeTypes := #[Ty.void, .ptr "one" false 1]
  let self : Global := {
    name := some "state", ty := 1, isConst := false, threadlocal := false,
    isExtern := false, init := some (.ptrConst 1 0 0)
  }
  let a := mkFunc "a" nodeTypes #[] 0 #[] #[self]
  let b := mkFunc "b" #[.ptr "one" false 0, .void] #[] 1 #[] #[{ self with ty := 0, init := some (.ptrConst 0 0 0) }]
  require (compatibleType a b 1 0) "recursive pointer type rejected"
  require (compatibleGlobal a b 0 0) "recursive global rejected"
  require (accepted (checkProgram #[a, b])) "recursive shared global rejected"
  require (rejected (checkProgram #[a, { b with globals := #[{ b.globals[0]! with isConst := true }] }])
    "inconsistent shared global 'state'") "global flag mutation accepted"
  require (rejected (checkProgram #[a, { b with globals := #[{ b.globals[0]! with init := some (.ptrConst 0 0 1) }] }])
    "inconsistent shared global 'state'") "recursive global value mutation accepted"
  let badGlobal := { self with name := some "a", init := some (.undef 1) }
  require (rejected (checkProgram #[{ a with globals := #[badGlobal] }]) "collides with a function name")
    "function/global collision accepted"
  require (rejected (checkProgram #[{ a with globals := #[{ self with name := none }] }])
    "unnamed mutable global") "unnamed mutable global accepted"
  let bogusFn := { self with name := some "a", init := some (.func "a" false) }
  require (rejected (checkProgram #[{ a with globals := #[bogusFn] }]) "function initializer")
    "mistyped function initializer accepted"
  let badConstant := mkFunc "badConstant" #[.bool, .void] #[] 1
    #[{ id := 0, ty := 1, op := .ret (.int 0 1) }]
  require (rejected (checkProgram #[badConstant]) "incompatible type or value form")
    "integer-form boolean constant accepted"
  let timer := mkFunc "timer" #[.void, .int false 64, .struct "time.Timer" "auto" #[],
    .ptr "one" false 2] #[] 0
  require (accepted (checkModelSignature timer "time.Timer.read" #[.undef 3] 1))
    "known Timer model signature rejected"
  require (rejected (checkModelSignature { timer with types := timer.types.set! 2 (.struct "Other" "auto" #[]) }
    "time.Timer.read" #[.undef 3] 1) "Timer pointer/u64") "wrong nominal Timer receiver accepted"
  require (rejected (checkModelSignature { timer with types := timer.types.set! 3 (.ptr "one" true 2) }
    "time.Timer.read" #[.undef 3] 1) "Timer pointer/u64") "const Timer receiver accepted"
  let fnTy := "fn (u32) u32"
  let indirect := mkFunc "indirect" #[.int false 32, .other fnTy, .ptr "one" true 1, .void]
    #[2, 0] 0 #[{ id := 0, ty := 2, op := .arg 0 }, { id := 1, ty := 0, op := .arg 1 },
      { id := 2, ty := 0, op := .call (.inst 0) #[.inst 1] }, { id := 3, ty := 3, op := .ret (.inst 2) }]
    #[{
      name := some "target", ty := 1, isConst := true, threadlocal := false,
      isExtern := false, init := some (.func "target" false)
    }]
  require (accepted (checkProgram #[indirect, target])) "known indirect function-pointer target rejected"
  require (rejected (checkProgram #[indirect, { target with params := #[], body := #[] }]) "expected 0")
    "indirect signature mutation accepted"
  let parseOK (s : String) := (StrictJson.parse s).toOption.isSome
  let duplicate (s : String) : Bool := match StrictJson.parse s with
    | .error e => decide ((e.splitOn "duplicate JSON object key").length > 1)
    | .ok _ => false
  require (parseOK "{\"a\":1,\"b\":{\"a\":2}}") "separate object keys rejected"
  require (duplicate "{\"x\":0,\"\\u0078\":1}") "escaped duplicate accepted"
  require (duplicate "{\"😀\":0,\"\\ud83d\\ude00\":1}") "surrogate-pair duplicate accepted"
  require (duplicate "{\"�\":0,\"\\ud800\":1}") "Lean replacement-character alias accepted"
  require (!parseOK "{\"x\":\"\\uZZZZ\"}") "invalid Unicode escape accepted"
  require (!parseOK "[1,]") "trailing comma accepted"
  require (!parseOK "1e999999999") "unbounded exponent accepted"
  require (!parseOK (String.join (List.replicate 129 "[") ++ "0" ++ String.join (List.replicate 129 "]")))
    "depth limit bypassed"
  require (parseOK (String.join (List.replicate 128 "[") ++ "0" ++ String.join (List.replicate 128 "]")))
    "depth boundary rejected"
  let mut dag : Array Ty := #[.int false 0]
  for _ in [:21] do
    let child := dag.size - 1
    dag := dag.push (.struct "Zero" "packed" #[("a", child), ("b", child)])
  require (Raw.packedWidth dag (dag.size - 1) == some 0) "shared zero-width DAG rejected"
  require (Raw.packedWidth #[.struct "Cycle" "packed" #[("self", 0)]] 0 == none)
    "direct packed-width cycle did not return none"
  require (Raw.packedWidth #[.enum "Missing" 99 true #[]] 0 == none)
    "direct unknown packed-width child accepted"
  let mut wide : Array Ty := #[.int false 1]
  for _ in [:16] do
    let child := wide.size - 1
    wide := wide.push (.struct "Wide" "packed" #[("a", child), ("b", child)])
  require (Raw.packedWidth wide (wide.size - 1) == some 65536) "exact shared width changed"
  require (rejected ((Raw.parsePackedLit "wide" wide #[("x", wide.size - 1)] ".{ .x = 0 }").map (fun _ => ()))
    "packed integer width exceeds") "oversized packed literal reached exponentiation"
  require (rejected ((Raw.parseHexNat "float" 1048576 "not-hex").map (fun _ => ()))
    "unsupported float width") "direct hex API did not reject unsupported width first"
  let enumGraph (signed : Bool) (bits : Nat) (fields : Array (String × Int)) :=
    validateTypeGraph "enum" #[.int signed bits, .enum "E" 0 true fields]
  require (accepted (enumGraph false 0 #[("zero", 0)])) "u0 enum zero rejected"
  require (rejected (enumGraph false 0 #[("one", 1), ("alsoOne", 1)]) "does not fit")
    "enum duplicate reported before fit"
  require (rejected (enumGraph false 0 #[("zero", 0), ("alsoZero", 0)]) "duplicate tag")
    "u0 duplicate accepted"
  require (accepted (enumGraph true 2 #[("min", -2), ("max", 1)])) "signed enum boundaries rejected"
  require (rejected (enumGraph true 2 #[("below", -3)]) "does not fit") "signed enum underflow accepted"
  require (rejected (enumGraph true 2 #[("above", 2)]) "does not fit") "signed enum overflow accepted"
  require (accepted (enumGraph false 1 #[("min", 0), ("max", 1)])) "unsigned enum boundaries rejected"
  require (rejected (enumGraph false 1 #[("negative", -1)]) "does not fit") "unsigned enum negative accepted"
  require (rejected (enumGraph false 1 #[("above", 2)]) "does not fit") "unsigned enum overflow accepted"
  let readChunks (text : String) : IO ((USize → IO ByteArray) × IO.Ref (Array Nat)) := do
    let remaining ← IO.mkRef text.toUTF8
    let requests ← IO.mkRef (#[] : Array Nat)
    let read (n : USize) : IO ByteArray := do
      requests.modify (·.push n.toNat)
      let bytes ← remaining.get
      let count := min 2 n.toNat
      remaining.set (bytes.extract count bytes.size)
      return bytes.extract 0 count
    return (read, requests)
  let (read, requests) ← readChunks "abcd"
  let bytes ← StrictJson.readBounded read 4
  require (bytes == "abcd".toUTF8 && (← requests.get) == #[5, 3, 1])
    "short-read boundary was not read to EOF"
  let (growingRead, growthRequests) ← readChunks "abcde"
  let exceeded ← try
    let _ : ByteArray ← StrictJson.readBounded growingRead 4
    pure false
  catch e => pure (decide ((e.toString.splitOn "AIR JSON exceeds 4 UTF-8 bytes").length > 1))
  require (exceeded && (← growthRequests.get) == #[5, 3, 1])
    "growth did not stop at limit plus one byte"
  let loaded := mkFunc "loaded" #[.int false 32, .ptr "one" false 0, .void] #[1] 0
    #[{ id := 0, ty := 1, op := .arg 0 }, { id := 1, ty := 2, op := .retLoad (.inst 0) }]
  require (accepted (checkProgram #[loaded])) "compatible loaded return rejected"
  require (rejected (checkProgram #[{ loaded with ret := 2 }]) "loaded return has an incompatible result type")
    "loaded return mismatch accepted"
  let notPointer := { loaded with params := #[0], body := #[
    { id := 0, ty := 0, op := .arg 0 }, { id := 1, ty := 2, op := .retLoad (.inst 0) }] }
  require (rejected (checkProgram #[notPointer]) "loaded return operand is not a pointer")
    "non-pointer loaded return accepted"
  let indexed := mkFunc "indexed" #[.int false 32, .int false 64, .void, .bool] #[0] 0
    #[{ id := 9, ty := 0, op := .arg 0 }, { id := 9, ty := 1, op := .arg 0 }]
  let index := indexed.operandTypes
  require (index.valTy? (.inst 9) == some 0 && indexed.valTy? (.inst 9) == some 0)
    "instruction index lost first-occurrence behavior"
  require (index.valTy? (.bool true) == some 3 && index.valTy? .void == some 2)
    "literal IDs were not indexed"
  require (rejected (checkProgram #[indexed]) "duplicate instruction id 9")
    "type index concealed duplicate instruction ID"
  let tupleTypes := #[Ty.int false 32, .int false 32, .tuple #[0], .void]
  let tupleGlobal : Global := {
    name := some "tuple", ty := 2, isConst := true, threadlocal := false,
    isExtern := false, init := some (.agg 2 #[.int 1 7])
  }
  let constantFn := mkFunc "constants" tupleTypes #[] 3 #[] #[tupleGlobal]
  require (accepted (checkProgram #[constantFn])) "distinct compatible local constant IDs rejected"
  require (rejected (checkProgram #[{ constantFn with types := tupleTypes.set! 1 (.int false 64) }])
    "incompatible type or value form") "distinct incompatible local constant IDs accepted"
  let badRange := { tupleGlobal with init := some (.agg 2 #[.int 0 (-1)]) }
  require (rejected (checkProgram #[{ constantFn with globals := #[badRange] }]) "integer constant does not fit")
    "same-ID shortcut skipped nested integer range validation"
  let badShape := { tupleGlobal with init := some (.agg 2 #[.bool true]) }
  require (rejected (checkProgram #[{ constantFn with globals := #[badShape] }]) "incompatible type or value form")
    "same-ID shortcut skipped nested form validation"
  let allocTypes := #[Ty.allocator, .int false 32, .ptr "one" false 1, .errorUnion 4 2,
    .errorSet (some #["OutOfMemory"]), .void, .int false 64, .ptr "slice" false 1, .errorUnion 4 7]
  let allocLayouts : Array Layout := (Array.replicate allocTypes.size ({} : Layout)).set! 1
    { size := some 4, align := some 4 }
  let allocLayouts := (allocLayouts.set! 2 { ptrAlign := some 4 }).set! 7 { ptrAlign := some 4 }
  let allocator := { (mkFunc "allocator" allocTypes #[] 5) with layouts := allocLayouts }
  let allocCases : Array (String × Array Val × TyId) := #[
      ("mem.Allocator.create__anon_1", #[Val.undef 0], 3),
      ("mem.Allocator.alloc__anon_1", #[Val.undef 0, .int 6 2], 8),
      ("mem.Allocator.alignedAlloc__anon_1", #[Val.undef 0, .int 6 2], 8),
      ("mem.Allocator.dupe__anon_1", #[Val.undef 0, .undef 7], 8)]
  for (callee, args, result) in allocCases do
    require (accepted (checkModelSignature allocator callee args result)) "allocator OutOfMemory result rejected"
    let openSet := { allocator with types := allocTypes.set! 4 (.errorSet none) }
    require (accepted (checkModelSignature openSet callee args result)) "open allocator error set rejected"
    for errors in #[#[], #["Unrelated"]] do
      let closed := { allocator with types := allocTypes.set! 4 (.errorSet (some errors)) }
      require (rejected (checkModelSignature closed callee args result) "error set admitting OutOfMemory")
        "closed allocator error set lacking OutOfMemory accepted"
  let head := { self with name := some "head", init := some (.ptrConst 1 1 0) }
  let tail := { self with name := some "tail", init := some (.ptrConst 1 1 0) }
  let graphA := mkFunc "graphA" nodeTypes #[] 0 #[] #[head, tail]
  let graphB := mkFunc "graphB" b.types #[] 1 #[] #[
    { tail with ty := 0, init := some (.ptrConst 0 0 0) },
    { head with ty := 0, init := some (.ptrConst 0 0 0) }]
  let some completed := compatibleGlobalCached graphA graphB 0 1
    | throw (IO.userError "successful recursive global cache comparison failed")
  require (completed.contains (0, 1) && completed.contains (1, 0) && completed.size == 2)
    "successful comparison did not publish every visited global pair"
  require ((compatibleGlobalCached graphA graphB 1 0 completed).map (fun (pairs : Std.HashSet (Nat × Nat)) => pairs.size) == some 2)
    "successful pair cache did not preserve recursive equality"
  let broken := { graphB with
    globals := graphB.globals.set! 0 { graphB.globals[0]! with init := some (.ptrConst 0 0 1) }
  }
  require ((compatibleGlobalCached graphA broken 0 1).isNone) "failed comparison published provisional pairs"
  let graphC := { broken with name := "graphC" }
  require (rejected (checkProgram #[graphA, graphB, graphC]) "inconsistent shared global 'tail'")
    "global cache leaked between ordered file-table pairs or changed the first error"
  let spawn := mkFunc "spawn" #[.int false 32, .tuple #[0], .struct "Thread.SpawnConfig" "auto" #[],
    .errorSet none, .thread, .errorUnion 3 4, .void] #[] 5 #[
      { id := 0, ty := 5, op := .call (.func "Thread.spawn__anon_1" false (some "target"))
          #[.undef 2, .agg 1 #[.int 0 7]] },
      { id := 1, ty := 6, op := .ret (.inst 0) }]
  require (accepted (checkProgram #[spawn, target])) "indexed spawn arguments rejected"
  require (rejected (checkProgram #[spawn, { target with params := #[], body := #[] }])
    "spawned callee 'target' has an incompatible argument count") "spawn argument index changed"
  let opaqueFn := mkFunc "opaque" #[.other "anyopaque", .ptr "one" true 0, .void] #[1] 2 #[
    { id := 0, ty := 1, op := .arg 0 }, { id := 1, ty := 2, op := .call (.inst 0) #[] },
    { id := 2, ty := 2, op := .ret .void }]
  require ((opaqueFn.calleeFnTy? 0).isNone) "opaque pointer was classified as a function pointer"
  require (rejected (checkProgram #[opaqueFn]) "inst 1: indirect callee is not a function pointer")
    "opaque indirect call accepted without targets"
  require (indirect.calleeFnTy? 0 == some fnTy) "known function pointer classification changed"
  let twice := { source with body := #[
    { id := 0, ty := 0, op := .arg 0 },
    { id := 1, ty := 0, op := .call (.func "target" false) #[.inst 0] },
    { id := 2, ty := 0, op := .call (.func "target" false) #[.inst 0] },
    { id := 3, ty := 1, op := .ret (.inst 2) }] }
  require (accepted (checkProgram #[twice, target])) "cached repeated signature rejected"
  let secondCall (args : Array Val) := { twice with
    body := twice.body.set! 2 { id := 2, ty := 0, op := .call (.func "target" false) args }
  }
  require (rejected (checkProgram #[secondCall #[], target]) "inst 2: callee 'target' has 0 arguments, expected 1")
    "cached signature concealed per-call arity"
  require (rejected (checkProgram #[secondCall #[.bool true], target]) "inst 2: callee 'target' has an incompatible argument 0")
    "cached signature concealed operand types"
  require (rejected (checkProgram #[secondCall #[.func "target" false], target]) "inst 2: callee 'target' argument 0: function values lack")
    "cached signature concealed unsupported function operands"
  let secondSource := { source with name := "secondSource", types := #[.int false 64, .void] }
  require (rejected (checkProgram #[source, secondSource, target]) "secondSource: inst 1: callee 'target' has an incompatible result")
    "signature cache leaked between source function tables"
  let boolTarget := mkFunc "boolTarget" #[.bool, .void] #[0] 1 #[
    { id := 0, ty := 0, op := .arg 0 }, { id := 1, ty := 1, op := .ret .void }]
  let boolSource := { (mkFunc "boolSource" #[.bool, .void] #[0] 1 #[
    { id := 0, ty := 0, op := .arg 0 },
    { id := 1, ty := 1, op := .call (.func "boolTarget" false) #[.bool true] },
    { id := 2, ty := 1, op := .call (.func "boolTarget" false) #[.inst 0] },
    { id := 3, ty := 1, op := .ret .void }]) with
      layouts := #[{ align := some 2 }, {}]
  }
  require (rejected (checkProgram #[boolSource, boolTarget]) "inst 2: callee 'boolTarget' has an incompatible argument 0")
    "untyped bool literal published a type/layout comparison"
  let nestedRoots := { constantFn with
    ret := 99
    body := #[{ id := 1, ty := 77, op := .ret (.undef 88) }]
    globals := #[{ tupleGlobal with init := some (.optSome 2 (.errUnionOk 2
      (.sliceConst 2 (.undef 55) (.agg 2 #[.undef 66])))) }]
  }
  for f in #[source, target, indirect, spawn, constantFn, graphA, graphB, nestedRoots] do
    let old := previousUsedTypes f
    let new := programUsedTypes f
    require (old.size == new.size && old.toArray.all new.contains) "streamed type closure changed reachable IDs"
  let roots := programUsedTypes nestedRoots
  require (#[99, 77, 88, 55, 66].all roots.contains) "streamed collector discarded unknown or nested type IDs"
  let headChanged := { graphB with
    globals := graphB.globals.set! 1 { graphB.globals[1]! with init := some (.ptrConst 0 0 1) }
  }
  for right in #[graphB, headChanged] do
    let some seed := previousGlobalCached graphA right 1 0
      | throw (IO.userError "known tail comparison did not establish a cache")
    let before := previousGlobalCached graphA right 0 1 seed
    let after := compatibleGlobalCached graphA right 0 1 seed
    require (before.isSome == after.isSome) "global cache cleanup changed success/failure"
    if let (some old, some new) := (before, after) then
      require (old.size == new.size && old.toArray.all new.contains) "global cache cleanup changed completed pairs"
    require (seed.size == 1 && seed.contains (1, 0) && !seed.contains (0, 1))
      "global comparison mutated the caller's completed cache"
  let some rejectedSeed := previousGlobalCached graphA headChanged 1 0
    | throw (IO.userError "unchanged tail comparison failed")
  require ((compatibleGlobalCached graphA headChanged 0 1 rejectedSeed).isNone)
    "cached successful type hid a changed pointer offset"
  let scalarGlobal : Global := {
    name := some "scalar", ty := 0, isConst := true, threadlocal := false,
    isExtern := false, init := some (.int 0 7)
  }
  let scalarA := mkFunc "scalarA" #[.int false 32, .void] #[] 1 #[] #[scalarGlobal]
  let scalarB := { scalarA with name := "scalarB" }
  let scalarChanged := { scalarB with globals := #[{ scalarGlobal with init := some (.int 0 8) }] }
  let layoutChanged := { scalarB with layouts := #[{ align := some 8 }, {}] }
  let tupleChanged := { constantFn with
    globals := #[{ tupleGlobal with init := some (.agg 2 #[.int 1 8]) }]
  }
  let compareCases : Array (Func × Func × Bool) := #[
      (scalarA, scalarB, true), (scalarA, scalarChanged, false),
      (scalarA, layoutChanged, false), (constantFn, constantFn, true),
      (constantFn, tupleChanged, false)]
  for (left, right, shouldAgree) in compareCases do
    let before := previousGlobalCached left right 0 0
    let after := compatibleGlobalCached left right 0 0
    require (before.isSome == shouldAgree && after.isSome == shouldAgree)
      "local successful type cache changed value/layout equality or leaked between file tables"
  IO.println "whole-program direct API and strict JSON checks passed"

#eval validationChecks
