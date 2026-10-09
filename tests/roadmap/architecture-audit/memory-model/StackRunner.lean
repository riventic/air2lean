-- Appended to the fresh `StackDepth` translation of stack_depth.zig (check.sh). MM-5: the
-- model charges each `depth` frame to a stack budget. Without one (`mem0`, premise STK-01)
-- `depth(n)` returns `n`; under the 8 MiB main-thread stack of the native run it overflows,
-- as the native ReleaseSafe build does.
private def report (name : String) (limit : Option Nat) (n : Nat) : IO Unit :=
  match ((StackDepth.depth (BitVec.ofNat 64 n)).run
      { StackDepth.mem0 with stackLimit := limit }).run with
  | some (.ok (v, _)) => IO.println s!"{name} {v.toNat}"
  | some (.error e) => IO.println s!"{name} error {reprStr e}"
  | none => IO.println s!"{name} diverges"

def main : IO Unit := do
  report "depth(1000)" none 1000
  report "depth(1000,8MiB)" (some (8 * 1024 * 1024)) 1000
  report "depth(10000000,8MiB)" (some (8 * 1024 * 1024)) 10000000
