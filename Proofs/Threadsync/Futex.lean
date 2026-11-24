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
  show (BitVec.ofNat 64 j).slt 0 = false
  rw [BitVec.slt, hi]
  exact decide_eq_false (by show ¬ ((j : Int) < (0 : BitVec 64).toInt); simp)

/-- The count a Linux wake returns (at most `2^31 − 1`) is `SUCCESS` for std's `E.init`. -/
theorem errno_count {j : Nat} (hj : j ≤ 2 ^ 31 - 1) :
    os_linux_errnoFromSyscall (BitVec.ofNat 64 j) = pure os_linux_E__enum_1.SUCCESS :=
  errno_nonneg (lt_count hj)

/-- `@min(max_waiters, maxInt(i32))` as a number. -/
theorem min_toNat (c : BitVec 32) :
    (Zig.min false (2147483647 : BitVec 32) c).toNat = min c.toNat (2 ^ 31 - 1) := by
  have h2 : (2147483647 : BitVec 32).toNat = 2147483647 := rfl
  show (if (2147483647 : BitVec 32).ule c = true then (2147483647 : BitVec 32) else c).toNat = _
  by_cases hle : (2147483647 : BitVec 32).ule c = true
  · have hn : (2147483647 : BitVec 32).toNat ≤ c.toNat := by simpa [BitVec.ule] using hle
    simp only [hle, ↓reduceIte]; rw [h2] at hn ⊢; omega
  · have hn : ¬ (2147483647 : BitVec 32).toNat ≤ c.toNat := by simpa [BitVec.ule] using hle
    simp only [hle, ↓reduceIte]; rw [h2] at hn; omega

/-- **`Thread.Futex.wake(p, c)`** (Linux, `c ≠ 0`) at a live word `p`: the OS wake of up to
`wakeLimit v` waiters at `p`'s private key, where `v = min(c, maxInt(i32))`; it returns after a
wake of `j ≤ 2^31 − 1` threads. -/
theorem wake_wp (hcost : P.cost = none) {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}
    {p : Ptr} {c : BitVec 32} (hc : c ≠ 0) (hword : m.wordAt p = true)
    {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ v : BitVec 32, v.toNat = min c.toNat (2 ^ 31 - 1) →
      P.WP t (Os.futexWake p false (some (Os.Linux.wakeLimit v)) false : ConcM Tgt (Option Nat))
        (fun r G' m' d' => ∃ j, r = some j ∧ j ≤ 2 ^ 31 - 1 ∧ Q () G' m' d') G m n) :
    P.WP t (Thread_Futex_wake p c) Q G m n := by
  have hc' : (c == (0 : BitVec 32)) = false := beq_false_of_ne hc
  have hM := min_toNat c
  generalize hMe : Zig.min false (2147483647 : BitVec 32) c = M at hM
  -- the two casts of the count (`u32` to `u31` to `u32`) keep its value
  have h31 : Zig.intCast false false 31 M false = pure (BitVec.ofNat 31 M.toNat) :=
    Zig.intCast_unsigned_of_lt (by rw [hM]; omega)
  have hv : ((BitVec.ofNat 31 M.toNat).setWidth 32).toNat = min c.toNat (2 ^ 31 - 1) := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hM]; omega
  have hcast1 : ∀ {Q' : BitVec 31 → (ThreadId → γ) → Mem → Nat → Prop} {G' : ThreadId → γ}
      {m' : Mem} {n' : Nat}, Q' (BitVec.ofNat 31 M.toNat) G' m' n' →
      P.WP t (ConcM.liftMem (StateT.lift (Zig.intCast false false 31 M false)) :
        ConcM Tgt (BitVec 31)) Q' G' m' n' :=
    fun hq => WP.liftMem_pure (by rw [h31]; rfl) rfl hq
  have hcast2 : ∀ {Q' : BitVec 32 → (ThreadId → γ) → Mem → Nat → Prop} {G' : ThreadId → γ}
      {m' : Mem} {n' : Nat}, Q' ((BitVec.ofNat 31 M.toNat).setWidth 32) G' m' n' →
      P.WP t (ConcM.liftMem (StateT.lift
        (Zig.intCast false false 32 (BitVec.ofNat 31 M.toNat) false)) :
        ConcM Tgt (BitVec 32)) Q' G' m' n' :=
    fun hq => WP.liftMem_pure
      (by rw [Zig.intCast_unsigned_widen _ 32 (by decide)]; rfl) rfl hq
  have herrno : ∀ {j : Nat}, j ≤ 2 ^ 31 - 1 →
      ∀ {Q' : os_linux_E__enum_1 → (ThreadId → γ) → Mem → Nat → Prop} {G' : ThreadId → γ}
      {m' : Mem} {n' : Nat}, Q' os_linux_E__enum_1.SUCCESS G' m' n' →
      P.WP t (ConcM.liftMem (StateT.lift (os_linux_errnoFromSyscall (BitVec.ofNat 64 j))) :
        ConcM Tgt os_linux_E__enum_1) Q' G' m' n' :=
    fun hj hq => WP.liftMem_pure (by rw [errno_count hj]; rfl) rfl hq
  have h' := h _ hv
  subst hMe
  unfold Thread_Futex_wake Thread_Futex_LinuxImpl_wake
  fsym [h', hcast1, hcast2, herrno, hc']

end_when

end Futex

end Threadsync
