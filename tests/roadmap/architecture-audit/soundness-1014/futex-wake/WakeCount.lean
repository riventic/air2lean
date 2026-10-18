import Air2Lean.StdModels
import ZigLean.Sep.Full.OsFutex

/-!
# Audit 2026-10-14, finding S5: the hand models' futex wake count is not the native one

`Thread.Futex.wake` (0.14.1, 0.15.2) and `Io.futexWake` (0.16.0, 0.17.0) are hand models (STD-05,
`Zig.threadFutexWakeC`, `Zig.futexWakeC`): the scheduler's `wake p n`, which wakes exactly
`min n k` of the `k` threads queued at `p` (`Thread.wakePick_length`). Std's code calls the OS:

* macOS: `__ulock_wake` with `WAKE_ALL` when `max_waiters > 1`, which wakes every waiter;
* Linux: `futex_3arg` with `@min(max_waiters, maxInt(i32))`; the kernel's `nr_wake` is an
  `int`, so at most `2^31 − 1` threads wake.

The OS models of these calls (OSF-02, `ZigLean/Os/Futex.lean`) have the native count. This file
elaborates while a std wake is still bound to the hand model (the last `#guard`); deleting the
rows (STD-05 steps D and E) makes it fail. `docs/architecture-audit/soundness-2026-10-14.md` §S5
has the impact analysis.
-/

open Zig Zig.Os

namespace AuditS5

def p0 : Ptr := ⟨some 0, 0⟩

/-- Three threads asleep at `p0`. -/
def three : Mem := { waiters := #[(1, p0), (2, p0), (3, p0)] }

/-- **The hand model** of `wake(p0, 2)` (`.wake p0 2`) leaves one of the three asleep, under every
choice of the oracle (the scheduler picks among the waiters left: `Sched.State.chooseWake`). -/
theorem hand_leaves_one : ∀ a < 3, ∀ b < 2,
    ((Thread.futexWake p0 2 [a, b]).run three).run.map
      (·.map fun (_, m) => (m.waitersAt p0).length) = some (.ok 1) := by decide +kernel

/-- **macOS**: std's `wake(p0, 2)` is `__ulock_wake(… | WAKE_ALL)`, whose every option that wakes
wakes all three (OSF-02). -/
theorem native_wakes_all : ∀ c < wakeCount p0 none three,
    ((wakeAt c p0 none).run three).run.map (·.map fun (n, m) => (n, m.waitersAt p0)) =
      some (.ok (some 3, [])) := by decide +kernel

/-- **Linux**: the kernel wakes at most `2^31 − 1` threads, whatever the count (`int nr_wake`)... -/
theorem native_clamp (v : BitVec 32) : Linux.wakeLimit v ≤ 2 ^ 31 - 1 := Linux.wakeLimit_le v

/-- ... while the hand model's `wake p (maxInt(u32))` wakes every one of `2^31` waiters. -/
theorem hand_wakes_more (l : List ThreadId) (hl : l.length = 2 ^ 31) (cs : List Nat) :
    (Thread.wakePick (2 ^ 32 - 1) l cs).length = 2 ^ 31 := by
  rw [Thread.wakePick_length, hl]; decide

-- The binding is still there: a std wake selects the hand model.
#guard Air2Lean.stdModels.any fun r => r.symbol == "Thread.Futex.wake" || r.symbol == "Io.futexWake"

end AuditS5
