import Proofs.Sync.Mailbox.Code
import Proofs.Sync.IoSemaphore
import ZigLean.Conc.RunResult

/-!
# The mailbox with the translated std semaphore: one completed run

`stdMain` and `stdDispatch` are the mailbox's code (`Proofs/Sync/Mailbox/Code.lean`) with the
translated `Io.Semaphore` (`Sync.ioSem`). Under the oracle that always picks option 0 the run
completes with 34, and the kernel computes it (`decide +kernel`). A loop (`Zig.loop`, a
`partial_fixpoint`) is not computed by the kernel: the proof unfolds the functions on the run's
path that hold one (`delta`) and then every loop four times by its defining equation
(`Zig.loop.eq_1`, one `simp` pass each), more than any loop of this run takes, so the kernel never
reaches a loop (the pattern of `tests/roadmap/sync-contracts/EventSet.lean`).
-/

open Zig Zig.Conc

namespace Sync.Mailbox

/-- The mailbox client with the translated std semaphore. -/
abbrev stdMain := mailMain ioSem

/-- The spawn targets with the translated std semaphore. -/
abbrev stdDispatch := dispatch ioSem

/-- **One schedule completes**: under the oracle that always picks option 0, the mailbox client
returns 34 within fuel 1000, from `mem0` with the translation's spawn policy. -/
theorem mailbox_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ stdDispatch 1000 (fun _ => 0) (stdMain ⟨⟩)
      (mem0 σ)) = some 34 := by
  refine ⟨.fresh, ?_⟩
  delta stdDispatch stdMain dispatch producer mailMain ioSem Io_Semaphore_waitUncancelable
    Io_Semaphore_post Io_Mutex_lockUncancelable Io_Condition_waitUncancelable
    Io_Condition_waitInner Io_Condition_waitInner.loop23 Io_Condition_signal
    Io_Semaphore_waitUncancelable.loop5 Io_Mutex_lockUncancelable.loop23
    Io_Condition_waitInner.loop56 Io_Condition_signal.loop11
  iterate 4 (simp (config := { singlePass := true, maxSteps := 200000 }) only [Zig.loop.eq_1])
  decide +kernel

end Sync.Mailbox
