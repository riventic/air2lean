import Proofs.Sync.Mutex

/-!
Concurrent clients: two threads increment a counter under an `Io.Mutex`. Every run that the
scheduler finishes returns 4, under every schedule.

From the repository root:
  lake build Proofs.Sync.Mutex
  lake env lean tutorials/concurrent-clients/Main.lean

See tutorials/concurrent-clients/README.md for the source, the exercise and the negative control.
-/

namespace ConcurrentClients

open Zig Zig.Conc Sync Sync.MutexCounter

/-- Every finished run (any oracle `o`, any `fuel`) succeeds and returns 4: `mutexCounter_safe`
rules out an error, `mutexCounter_spec` fixes the value. -/
theorem finished_run_returns_four (env : Env) (henv : env.spawn = .available) (io : Io) (fuel : Nat)
    (o : Nat → Nat)
    (r : Except Error (Except ErrName (BitVec 32) × Mem))
    (finished : (Sched.run env dispatch fuel o (mutexCounter io) mem0).run = some r) :
    ∃ m, r = .ok (.ok 4, m) := by
  cases r with
  | error e => exact absurd finished (mutexCounter_safe env henv io)
  | ok vm =>
    obtain ⟨v, m⟩ := vm
    exact ⟨m, by rw [mutexCounter_spec env henv io finished]⟩

end ConcurrentClients
