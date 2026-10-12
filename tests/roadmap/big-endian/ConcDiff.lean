import ConcRun

/-! The lines of `concurrency_native.zig` but the futex case (`ConcRun.lean`). -/

open Zig Conc

def main : IO Unit := do
  let line (name s : String) : IO Unit := IO.println s!"{name}: {s}"
  line "storeThenBytes" (runAll bv (storeThenBytes 0x01020304))
  line "bytesThenLoad" (runAll bv (bytesThenLoad 1 2 3 4))
  line "rmwCarryByte0" (runAll bv (rmwCarryByte0 0x00FF 0x0001))
  line "casSwap" (runAll bv (casSwap 0x0102030405060708 0x1112131415161718))
  line "rmwMax" (runAll (fun v => toString v.toInt) (rmwMax (BitVec.ofInt 32 (-5)) 3))
  line "threadsAdd" (runAll ebv (threadsAdd 3))
  line "heapWord" (runAll ebv (heapWord default 0x0A0B0C0D))
