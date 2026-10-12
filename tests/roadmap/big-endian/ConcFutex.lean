import ConcRun

/-! The futex case of `concurrency.zig` (`std.Thread.Futex`: Zig 0.14.1 and 0.15.2), after the
lines of `ConcDiff.lean` (`ConcRun.lean`). The expected value is the word's bytes in the other order, so the wait
returns at once; under a byte-order mistake the model would sleep forever (`.deadlock`). -/

open Zig Conc

def main : IO Unit :=
  IO.println s!"futexNoSleep: {runAll bv futexNoSleep}"
