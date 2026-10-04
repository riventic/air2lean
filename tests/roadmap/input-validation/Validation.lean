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

#eval do
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
    let _ ← StrictJson.readBounded growingRead 4
    pure false
  catch e => pure (decide ((e.toString.splitOn "AIR JSON exceeds 4 UTF-8 bytes").length > 1))
  require (exceeded && (← growthRequests.get) == #[5, 3, 1])
    "growth did not stop at limit plus one byte"
  IO.println "whole-program direct API and strict JSON checks passed"
