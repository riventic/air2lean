import Proofs.Threadsync.Variant
import ZigLean.Sep.Full.OsFutex
import ZigLean.Sep.Full.AutoWP

/-!
# `Thread.Futex.wake` of `examples/threadsync` down to the OS wake (0.15.2, premise OSF-02)

`Thread.Futex.wake` is translated std code (audit soundness-2026-10-14 §S6 finding 4, step D): it
reaches the kernel's futex queue only through the OS row of its target. This file reduces a call
of it at a live word to the OS wake (`Os.futexWake`), for every protocol; the callers
(`Thread.Mutex.unlock`, `ResetEvent.set`, `Condition.signal`) then take the step with the rule of
their primitive at the OS wake (`FLock.wp_osWake`, `FEvent.wp_osWake`, `FCond.wp_osWakeEp`).

- **Linux** (`LinuxImpl.wake`): `futex_3arg(ptr, WAKE | PRIVATE, @min(max_waiters, maxInt(i32)))`,
  so it wakes at most `min(max_waiters, 2^31 − 1)` threads; the count the kernel returns is not an
  errno (`errno_count`), so the `else => unreachable` of std's `switch` is not reached.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full

namespace Threadsync

-- Unification must not unfold `WP` into the generated program.
attribute [local irreducible] Proto.WP

namespace Futex

variable {γ : Type} {P : Proto Tgt γ}

when_defined Thread_Futex_LinuxImpl_wake

/-- A syscall result that is not negative as an `isize` is no errno: `errnoFromSyscall` is
`SUCCESS`. -/
theorem errno_nonneg {x : BitVec 64} (h : Zig.lt true x (0 : BitVec 64) = false) :
    os_linux_errnoFromSyscall x = pure os_linux_E__enum_1.SUCCESS := by
  unfold os_linux_errnoFromSyscall
  cases hg : Zig.gt true x (-(4096 : BitVec 64)) <;> simp only [pure_bind, h, hg] <;> rfl

/-- A count of woken threads within the kernel's `int` is not negative as an `isize`. -/
theorem lt_count {j : Nat} (hj : j ≤ 2 ^ 31 - 1) :
    Zig.lt true (BitVec.ofNat 64 j) (0 : BitVec 64) = false := by
  have hn : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hi : (BitVec.ofNat 64 j).toInt = (j : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hn]; omega), hn]
  show (if true = true then (BitVec.ofNat 64 j).slt 0 else (BitVec.ofNat 64 j).ult 0) = false
  rw [if_pos rfl, BitVec.slt, hi]
  exact decide_eq_false (by show ¬ ((j : Int) < (0 : BitVec 64).toInt); simp)

/-- **`Thread.Futex.wake(p, c)`** (Linux, `c ≠ 0`) at a live word `p`: the OS wake of up to
`wakeLimit v` waiters at `p`'s private key, where `v = min(c, maxInt(i32))`; it returns after a
wake of `j ≤ 2^31 − 1` threads. -/
theorem wake_wp (hcost : P.cost = none) {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}
    {p : Ptr} {c : BitVec 32} (hc : c ≠ 0) (hword : m.wordAt p = true)
    {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ v : BitVec 32, v.toNat = Nat.min c.toNat (2 ^ 31 - 1) →
      P.WP t (Os.futexWake p false (some (Os.Linux.wakeLimit v)) false : ConcM Tgt (Option Nat))
        (fun r G' m' d' => ∃ j, r = some j ∧ j ≤ 2 ^ 31 - 1 ∧ Q () G' m' d') G m n) :
    P.WP t (Thread_Futex_wake p c) Q G m n := by
  have hc' : (c == (0 : BitVec 32)) = false := beq_false_of_ne hc
  unfold Thread_Futex_wake Thread_Futex_LinuxImpl_wake
  fsym [h, errno_nonneg, lt_count, hc']

end_when

end Futex

end Threadsync
