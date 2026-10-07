import Proofs.Sync.Mutex

/-! Exercise solution: no schedule loses an increment, so no finished run returns 3. -/

namespace ConcurrentClients

open Zig Zig.Conc Sync Sync.MutexCounter

theorem never_three (io : Io) (fuel : Nat) (o : Nat → Nat) (m : Mem) :
    (Sched.run dispatch fuel o (mutexCounter io) mem0).run ≠ some (.ok (.ok 3, m)) := by
  intro finished
  have h := mutexCounter_spec io finished
  simp at h

end ConcurrentClients
