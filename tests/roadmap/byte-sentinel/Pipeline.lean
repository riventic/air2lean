import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
open Lean Air2Lean
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) := obj [("inst", num n)]
private def intTy (bits : Nat) := obj [("k", .str "int"), ("signed", .bool false),
  ("bits", num bits), ("abi_size", num (Zig.intSize bits)), ("abi_align", num (Zig.intAlign bits))]
private def pointer (sentinel : Bool := true) (value : Option String := some "42")
    (align : Nat := 1) (isConst : Bool := false) :=
  obj ([("k", .str "ptr"), ("size", .str "slice"), ("const", .bool isConst),
    ("child", num 2), ("sentinel", .bool sentinel), ("ptr_align", num align),
    ("abi_size", num 16), ("abi_align", num 8)] ++
    (value.toList.map fun s => ("sentinel_byte", .str s)))
private def types (ptr : Json) (bits : Nat := 8) :=
  #[obj [("k", .str "struct"), ("name", .str "mem.Allocator"), ("abi_size", num 16), ("abi_align", num 8)],
    intTy 64, intTy bits, ptr,
    obj [("k", .str "error_set"), ("errors", .arr #[.str "OutOfMemory"]), ("abi_size", num 2), ("abi_align", num 2)],
    obj [("k", .str "error_union"), ("error", num 4), ("payload", num 3), ("abi_size", num 24), ("abi_align", num 8)],
    obj [("k", .str "noreturn")], obj [("k", .str "optional"), ("child", num 3), ("abi_size", num 24), ("abi_align", num 8)]]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def input (ptr : Json) (bits : Nat := 8) (remap : Bool := false) :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("name", .str "make"),
    ("types", .arr (types ptr bits)), ("params", toJson (if remap then #[0, 3, 1] else #[0, 1])),
    ("ret", num (if remap then 7 else 5)), ("body", .arr
      (if remap then #[inst 0 "arg" 0 #[] [("param", num 0)],
        inst 1 "arg" 3 #[] [("param", num 1)], inst 2 "arg" 1 #[] [("param", num 2)],
        inst 3 "call" 7 #[ref 0, ref 1, ref 2]
          [("callee", obj [("func", .str "mem.Allocator.remap__anon_1")])], inst 4 "ret" 6 #[ref 3]]
      else #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "arg" 1 #[] [("param", num 1)],
        inst 2 "call" 5 #[ref 0, ref 1]
          [("callee", obj [("func", .str "mem.Allocator.allocSentinel__anon_1")])], inst 3 "ret" 6 #[ref 2]]))]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  checkProgram #[f]
  pure f
private def reject (j : Json) (expected : String) : IO Unit := do
  match process j with
  | .ok _ => throw (IO.userError s!"accepted negative fixture: {expected}")
  | .error e => unless (e.splitOn expected).length > 1 do
      throw (IO.userError s!"wrong rejection: {e}; expected {expected}")

/-- Bypass JSON deliberately: normalized API clients must receive the same admission guards. -/
private def rejectNormalized (f : Func) (layout : Layout) (expected : String) : IO Unit := do
  let changed := { f with layouts := f.layouts.set! 3 layout }
  match checkModelSignature changed "mem.Allocator.allocSentinel__anon_1" #[.inst 0, .inst 1] 5 with
  | .ok _ => throw (IO.userError s!"accepted normalized rejection fixture: {expected}")
  | .error e => unless (e.splitOn expected).length > 1 do
      throw (IO.userError s!"wrong normalized rejection: {e}; expected {expected}")

def main : IO Unit := do
  for value in ["0", "42", "255"] do
    let f ← match process (input (pointer true (some value))) with
      | .ok f => pure f | .error e => throw (IO.userError e)
    let source := emit #[f] "Sentinel" ""
    unless (source.splitOn s!"({value}#8)").length > 1 &&
        (source.splitOn "Zig.Allocator.allocSentinel").length > 1 do
      throw (IO.userError "emitter lost the explicit comptime sentinel")
  reject (input (pointer true none)) "explicit exported sentinel_byte"
  reject (input (pointer false none)) "byte sentinel slice with alignment 1"
  reject (input (pointer true (some "42") 2)) "byte sentinel slice with alignment 1"
  reject (input (pointer true (some "42") 1 true)) "mutable byte sentinel slice result"
  reject (input (pointer true none) 16) "allocSentinel supports only u8"
  reject (input (pointer true (some "256"))) "sentinel_byte must be in 0..255"
  reject (input (pointer true (some "-1"))) "sentinel_byte must be decimal byte text"
  reject (input (pointer false (some "42"))) "sentinel_byte requires sentinel=true"
  reject (input (pointer true (some "42")) 8 true) "a remap of a slice with a sentinel"
  reject ((input (pointer)).setObjVal! "zig_version" (.str "0.15.2")) "allocSentinel qualified Zig 0.16.0"
  let base ← match process (input (pointer)) with
    | .ok f => pure f | .error e => throw (IO.userError e)
  let l := base.layouts[3]!
  rejectNormalized base { l with sentinelByte := some 256 } "sentinel_byte in 0..255"
  rejectNormalized base { l with hostSize := 1 } "ordinary byte sentinel pointer without packed metadata"
  rejectNormalized base { l with bitOffset := 1 } "ordinary byte sentinel pointer without packed metadata"
  let zero := { base with layouts := base.layouts.set! 3 { l with sentinelByte := some 0 } }
  unless !(sameSpawnTy base zero 3 3) && sameSpawnTy base base 3 3 do
    throw (IO.userError "spawned pointer compatibility lost the exact known byte sentinel")
  let legacy := { base with layouts := base.layouts.set! 3 { l with sentinelByte := none } }
  unless !(sameSpawnTy base legacy 3 3) && !(sameSpawnTy legacy base 3 3) &&
      sameSpawnTy legacy legacy 3 3 do
    throw (IO.userError "spawn compatibility did not distinguish known and missing sentinel metadata")
  -- The public capture checker must apply the same rule, not just the comparison helper.
  let capture := { base with types := base.types.push (.tuple #[3]) }
  let legacyCapture := { legacy with types := legacy.types.push (.tuple #[3]) }
  let worker := { base with name := "sentinelWorker", params := #[3], ret := 6 }
  let legacyWorker := { worker with layouts := legacy.layouts }
  let zeroWorker := { worker with layouts := zero.layouts }
  let captures : Array Val := #[.void, .agg 8 #[.undef 3]]
  for (caller, target) in #[(capture, zeroWorker), (capture, legacyWorker), (legacyCapture, worker)] do
    match checkThreadSpawn caller target "Thread.spawn" 1 captures with
    | .ok _ => throw (IO.userError "accepted incompatible sentinel capture through public API")
    | .error e => unless (e.splitOn "does not match worker").length > 1 do
        throw (IO.userError s!"wrong sentinel capture rejection: {e}")
  unless (checkThreadSpawn capture worker "Thread.spawn" 1 captures).toOption.isSome &&
      (checkThreadSpawn legacyCapture legacyWorker "Thread.spawn" 1 captures).toOption.isSome do
    throw (IO.userError "rejected equal known or both-missing legacy sentinel captures")
  IO.println "3 explicit sentinel emissions; 10 parsed and 3 normalized rejections; known spawn sentinel checks"
