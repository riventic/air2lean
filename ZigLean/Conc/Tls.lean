import ZigLean.Conc.Basic
import ZigLean.Mem.Tls

/-!
# A spawned thread with thread-local storage

The generated dispatcher of a program with `threadlocal` globals runs each spawn target in
`ConcM.tlsThread tlsInit`: the thread makes its instances first (`tlsEnter`) and frees them
after the target returns (`tlsExit`), so the instances live exactly as long as the thread
(`ZigLean/Mem/Tls.lean`). A target that throws ends the whole run, so it needs no exit step.
-/

namespace Zig

/-- Run `body` as a thread with its own instances of the `threadlocal` globals `inits`. -/
def ConcM.tlsThread {Tgt : Type} (inits : List (BlockId × Array Byte × Nat))
    (body : ConcM Tgt Unit) : ConcM Tgt Unit := do
  ConcM.liftMem (tlsEnter inits)
  body
  ConcM.liftMem tlsExit

end Zig
