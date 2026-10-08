import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
open Lean Air2Lean

/-! C07: synthetic AIR for `Thread.detach` recognition (an E04 table row, Zig 0.16.0 only). A
function that detaches a `Thread` handle is admitted and emitted as `Zig.detachC`; a call of
another version or with an incompatible signature is rejected with its reason. The first
argument names the file that receives the emitted module (checked with `lake env lean -R`).
Run with `lake env lean --run tests/roadmap/detached-threads/Pipeline.lean <dir>/Detach.lean`. -/
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) := obj [("inst", num n)]
private def types (twoArgs : Bool) :=
  #[obj [("k", .str "struct"), ("name", .str "Thread"), ("abi_size", num 8), ("abi_align", num 8)],
    obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)],
    obj [("k", .str "noreturn")],
    obj [("k", .str "other"), ("name", .str (if twoArgs then "fn (Thread, Thread) void" else "fn (Thread) void"))]]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
/-- `fn launch(t: Thread) void { t.detach(); }`. -/
private def input (version : String := "0.16.0") (callee : String := "Thread.detach")
    (twoArgs : Bool := false) :=
  obj [("schema", num 11), ("zig_version", .str version), ("name", .str "detached.launch"),
    ("types", .arr (types twoArgs)), ("params", toJson #[0]), ("ret", num 1),
    ("body", .arr #[inst 0 "arg" 0 #[] [("param", num 0)],
      inst 1 "call" 1 (if twoArgs then #[ref 0, ref 0] else #[ref 0])
        [("callee", obj [("ty", num 3), ("func", .str callee), ("noreturn", .bool false)])],
      inst 2 "ret" 2 #[ref 1]])]
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

def main (args : List String) : IO Unit := do
  let f ← match process input with
    | .ok f => pure f | .error e => throw (IO.userError e)
  let source := emit #[f] "Detached" "detached."
  unless (source.splitOn "Zig.detachC p0").length > 1 do
    throw (IO.userError s!"detach was not emitted as the model call:\n{source}")
  unless (source.splitOn "Zig.ConcM").length > 1 do
    throw (IO.userError s!"a detaching function is not a concurrent function:\n{source}")
  reject (input (version := "0.15.2")) "Thread.detach qualified Zig 0.16.0"
  reject (input (twoArgs := true)) "argument count (2, expected 1)"
  -- `Io.futexWaitTimeout` stays an explicit rejection.
  reject (input (callee := "Io.futexWaitTimeout")) "outside the subset"
  if let some path := args.head? then IO.FS.writeFile path source
  IO.println "detached-thread pipeline checks passed"
