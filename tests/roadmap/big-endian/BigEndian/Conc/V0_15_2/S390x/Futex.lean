import BigEndian.Conc.V0_15_2.S390x.Run

/-! The futex case of `concurrency.zig` (`std.Thread.Futex`: Zig 0.14.1 and 0.15.2), after the
lines of `Diff.lean` (`Run.lean`). The expected value is the word's bytes in the other order, so
the wait returns at once; under a byte-order mistake the model would sleep forever (`.deadlock`).
Written for x86_64-linux; the other targets' modules are this one with the target renamed. -/

open Zig BigEndian.Conc.V0_15_2.S390x BigEndian.Conc.V0_15_2.S390x.Run

namespace BigEndian.Conc.V0_15_2.S390x.Futex

def main : IO Unit :=
  IO.println s!"futexNoSleep: {runAll bv futexNoSleep}"

end BigEndian.Conc.V0_15_2.S390x.Futex
