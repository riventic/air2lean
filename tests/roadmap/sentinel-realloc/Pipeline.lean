import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
open Lean Air2Lean

/-! Synthetic AIR for `mem.Allocator.realloc` recognition (E04 table row, Zig 0.16.0 only):
admitted for alignment-1 nonsentinel `[]u8`, emitted as `Zig.Allocator.realloc`; every other
shape is rejected with its reason. Fresh-source qualification is `check.sh`. -/
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) := obj [("inst", num n)]
private def intTy (bits : Nat) := obj [("k", .str "int"), ("signed", .bool false),
  ("bits", num bits), ("abi_size", num (Zig.intSize bits)), ("abi_align", num (Zig.intAlign bits))]
private def slice (sentinel : Bool := false) (align : Nat := 1) :=
  obj ([("k", .str "ptr"), ("size", .str "slice"), ("const", .bool false),
    ("child", num 2), ("sentinel", .bool sentinel), ("ptr_align", num align),
    ("abi_size", num 16), ("abi_align", num 8)] ++
    (if sentinel then [("sentinel_byte", .str "0")] else []))
private def types (ptr : Json) (bits : Nat) :=
  #[obj [("k", .str "struct"), ("name", .str "mem.Allocator"), ("abi_size", num 16), ("abi_align", num 8)],
    intTy 64, intTy bits, ptr,
    obj [("k", .str "error_set"), ("errors", .arr #[.str "OutOfMemory"]), ("abi_size", num 2), ("abi_align", num 2)],
    obj [("k", .str "error_union"), ("error", num 4), ("payload", num 3), ("abi_size", num 24), ("abi_align", num 8)],
    obj [("k", .str "noreturn")],
    obj [("k", .str "optional"), ("child", num 3), ("abi_size", num 24), ("abi_align", num 8)]]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def input (ptr : Json := slice) (bits : Nat := 8) (version : String := "0.16.0")
    (ret : Nat := 5) (twoArgs : Bool := false) :=
  obj [("schema", num 11), ("zig_version", .str version), ("name", .str "grow"),
    ("types", .arr (types ptr bits)), ("params", toJson #[0, 3, 1]), ("ret", num ret),
    ("body", .arr #[inst 0 "arg" 0 #[] [("param", num 0)],
      inst 1 "arg" 3 #[] [("param", num 1)], inst 2 "arg" 1 #[] [("param", num 2)],
      inst 3 "call" ret (if twoArgs then #[ref 0, ref 1] else #[ref 0, ref 1, ref 2])
        [("callee", obj [("func", .str "mem.Allocator.realloc__anon_1")])],
      inst 4 "ret" 6 #[ref 3]])]
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

def main : IO Unit := do
  let f ← match process input with
    | .ok f => pure f | .error e => throw (IO.userError e)
  let source := emit #[f] "SentinelRealloc" ""
  unless (source.splitOn "Zig.Allocator.realloc p0 p1 p2").length > 1 do
    throw (IO.userError s!"realloc was not emitted as the model call:\n{source}")
  reject (input (slice true)) "a realloc of a slice with a sentinel is outside the subset"
  reject (input slice 16) "realloc supports only u8"
  reject (input (slice false 2)) "byte slice with alignment 1"
  reject (input (version := "0.15.2")) "mem.Allocator.realloc qualified Zig 0.16.0"
  reject (input (ret := 7)) "error set admitting OutOfMemory"
  reject (input (twoArgs := true)) "argument count (2, expected 3)"
  IO.println "realloc pipeline: 1 emission; 6 parsed rejections"
