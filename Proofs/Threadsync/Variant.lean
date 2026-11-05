import ZigLean.VersionGate
import Proofs.Threadsync.Gen

/-!
# The OS variant of `Thread.Mutex` in this program's translation (0.15.2)

The translation of `Thread.Mutex` depends on the OS (`tests/golden/0.15.2/threadsync/Gen-darwin.lean`):
Linux has `FutexImpl` (contended value `3`), macOS `DarwinImpl` (`os_unfair_lock`, the word is only
`0` or `1`). The code of the other translation does not exist, so `when_defined`
(`ZigLean/VersionGate.lean`) checks the translation before it compiles the commands that name it.
Used by the proofs over full-state resources (`Proofs/Threadsync/ThreadMutex.lean`).
-/

namespace Threadsync

when_defined Thread_Mutex_FutexImpl_lock
/-- The contended value of the mutex word (Linux `FutexImpl`). The lock of the proofs has this
`c`. -/
def mutexC : Nat := 3

/-- The `Thread.Mutex` with the word `w`. -/
abbrev mutexOf (w : BitVec 32) : Thread_Mutex := { impl := { state := { raw := w } } }
end_when

when_defined Thread_Mutex_DarwinImpl
/-- The contended value of the mutex word (macOS: the word is only `0` or `1`). The lock of the
proofs has this `c`. -/
def mutexC : Nat := 1

/-- The `Thread.Mutex` with the word `w`. -/
abbrev mutexOf (w : BitVec 32) : Thread_Mutex :=
  { impl := { oul := { _os_unfair_lock_opaque := w } } }
end_when

end Threadsync
