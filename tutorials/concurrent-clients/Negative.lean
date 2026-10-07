import Proofs.Sync.Mutex

/-! Negative control: Lean must reject this file. A lost update (result 3) is impossible, so
the proof of `finished_run_returns_four` leaves `4 = 3` unsolved. -/
-- expect-error: unsolved goals

namespace ConcurrentClients

open Zig Zig.Conc Sync Sync.MutexCounter

theorem finished_run_returns_three (io : Io) (fuel : Nat) (o : Nat → Nat)
    (r : Except Error (Except ErrName (BitVec 32) × Mem))
    (finished : (Sched.run dispatch fuel o (mutexCounter io) mem0).run = some r) :
    ∃ m, r = .ok (.ok 3, m) := by
  cases r with
  | error e => exact absurd finished (mutexCounter_safe io)
  | ok vm =>
    obtain ⟨v, m⟩ := vm
    exact ⟨m, by rw [mutexCounter_spec io finished]⟩

end ConcurrentClients
