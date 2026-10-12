-- Appended to the fresh `StackDepth` translation of stack_depth.zig (check.sh). MM-5/MM-16: the
-- model charges each `depth` frame and its stack block to the main thread's stack budget
-- (`Mem.withStack`). Without one (`mem0 .fresh`, premise STK-01) `depth(n)` returns `n`; under
-- the 8 MiB main-thread stack of the native run it overflows, as the native ReleaseSafe build does.
private def report (name : String) (limit : Option Nat) (n : Nat) : IO Unit :=
  let m := StackDepth.mem0 .fresh
  match ((StackDepth.depth (BitVec.ofNat 64 n)).run
      (match limit with | some S => m.withStack S | none => m)).run with
  | some (.ok (v, _)) => IO.println s!"{name} {v.toNat}"
  | some (.error e) => IO.println s!"{name} error {reprStr e}"
  | none => IO.println s!"{name} diverges"

def main : IO Unit := do
  report "depth(1000)" none 1000
  report "depth(1000,8MiB)" (some (8 * 1024 * 1024)) 1000
  report "depth(10000000,8MiB)" (some (8 * 1024 * 1024)) 10000000
