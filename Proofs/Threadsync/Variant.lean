import Lean.Elab.Command
import Proofs.Threadsync.Gen

/-!
# The OS variant of `Thread.Mutex` in this program's translation (0.15.2)

The translation of `Thread.Mutex` depends on the OS (`tests/golden/0.15.2/threadsync/Gen-darwin.lean`):
Linux has `FutexImpl` (contended value `3`), macOS `DarwinImpl` (`os_unfair_lock`, the word is only
`0` or `1`). The code of the other translation does not exist, so `if_decl` checks the translation
before it compiles the commands that name it. Shared by the proofs over the legacy thread logic
(`Proofs/Threadsync/Lock.lean`) and over full-state resources (`Proofs/Threadsync/ThreadMutex.lean`).
-/

namespace Threadsync

/-- Compile the commands only if the translation declares `id` (the `Thread.Mutex` of one OS). -/
elab "if_decl " id:ident " in " cmds:command* " end_if" : command => do
  let found ← Lean.Elab.Command.liftCoreM
    (try discard <| Lean.resolveGlobalConstNoOverload id; pure true catch _ => pure false)
  if found then cmds.forM Lean.Elab.Command.elabCommand

if_decl Thread_Mutex_FutexImpl_lock in
/-- The contended value of the mutex word (Linux `FutexImpl`). The lock of the proofs has this
`c`. -/
def mutexC : Nat := 3

/-- The `Thread.Mutex` with the word `w`. -/
abbrev mutexOf (w : BitVec 32) : Thread_Mutex := { impl := { state := { raw := w } } }
end_if

if_decl Thread_Mutex_DarwinImpl in
/-- The contended value of the mutex word (macOS: the word is only `0` or `1`). The lock of the
proofs has this `c`. -/
def mutexC : Nat := 1

/-- The `Thread.Mutex` with the word `w`. -/
abbrev mutexOf (w : BitVec 32) : Thread_Mutex :=
  { impl := { oul := { _os_unfair_lock_opaque := w } } }
end_if

end Threadsync
