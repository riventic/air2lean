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
    simp only [hle, Bool.false_eq_true, ↓reduceIte]; rw [h2] at hn; omega

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
  have herrno : ∀ {j : Nat}
      {Q' : os_linux_E__enum_1 → (ThreadId → γ) → Mem → Nat → Prop} {G' : ThreadId → γ}
      {m' : Mem} {n' : Nat}, j ≤ 2 ^ 31 - 1 → Q' os_linux_E__enum_1.SUCCESS G' m' n' →
      P.WP t (ConcM.liftMem (StateT.lift (os_linux_errnoFromSyscall (BitVec.ofNat 64 j))) :
        ConcM Tgt os_linux_E__enum_1) Q' G' m' n' :=
    fun hj hq => WP.liftMem_pure (by rw [errno_count hj]; rfl) rfl hq
  have h' := h _ hv
  subst hMe
  unfold Thread_Futex_wake Thread_Futex_LinuxImpl_wake
  fsym [h', hcast1, hcast2, herrno, hc']
  -- the woken count `(some j).getD 0` is `j`
  assumption

end_when

when_defined Thread_Futex_DarwinImpl_wake

/-- `UL{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true, .WAKE_ALL = all }` as the `u32` the kernel
reads (`COMPARE_AND_WAIT | NO_ERRNO`, with `WAKE_ALL`). -/
theorem ul_bits (all : Bool) :
    Zig.Packed.toBits
      (⟨c_darwin_UL_Op.COMPARE_AND_WAIT, all, false, 0, false, false, false, 0, true, 0⟩ :
        c_darwin_UL) =
      (if all then Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Os.Darwin.UL_WAKE_ALL
        else Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO) := by
  cases all <;> decide

/-- The request of a macOS wake of `c ≠ 0` waiters: one waiter, or all (`WAKE_ALL`) for more
than one. -/
theorem wakeMax_ul (all : Bool) :
    Os.Darwin.wakeMax (if all then Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Os.Darwin.UL_WAKE_ALL
      else Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO) = if all then none else some 1 := by
  cases all <;> decide

/-- **`__ulock_wake`** of std's macOS wake, by a caller that supplies the steps of its primitive
at an invariant `I` of the wake's place: the oracle stop before the wake (`hpick`) and the OS
wake (`hwake`: done, `D`, after a wake of some `j` waiters; still at `I` after a spurious
`EINTR`). Its code is `0` or `-ENOENT` (`0xfffffffe`) when done, `-EINTR` (`0xfffffffc`) at
`I`. -/
theorem ulock_wake_wp {t : ThreadId} {p : Ptr} {all : Bool} {op : BitVec 32}
    {I D : (ThreadId → γ) → Mem → Prop}
    (hop : op = (if all then Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Os.Darwin.UL_WAKE_ALL
      else Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO))
    (hword : ∀ G m, I G m → m.wordAt p = true)
    (hpick : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Nat → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ k, d = k + 1 → ∀ a G₁ m', I G₁ m' → Q a G₁ m' k) →
      P.WP t (Os.pick (fun _ => 2) : ConcM Tgt Nat) Q G m d)
    (hwake : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ k, d = k + 1 → ∀ r G₁ m', ((∃ j, r = some j) ∧ D G₁ m' ∨ r = none ∧ I G₁ m') →
        Q r G₁ m' k) →
      P.WP t (Os.futexWake p false (if all then none else some 1) true :
        ConcM Tgt (Option Nat)) Q G m d)
    {G : ThreadId → γ} {m : Mem} {d : Nat} {Q : BitVec 32 → (ThreadId → γ) → Mem → Nat → Prop}
    (hI : I G m)
    (h : ∀ k, k < d → ∀ s G₁ m',
      ((s = 0 ∨ s = (0xfffffffe : BitVec 32)) ∧ D G₁ m' ∨
       s = (0xfffffffc : BitVec 32) ∧ I G₁ m') → Q s G₁ m' k) :
    P.WP t (Os.Darwin.__ulock_wake op (some p) 0 : ConcM Tgt (BitVec 32)) Q G m d := by
  subst hop
  refine WP.ulock_wake (by cases all <;> simp) (hword G m hI)
    (hpick hI fun k hk live G₁ m₁ hI₁ => ?_)
  rw [wakeMax_ul]
  refine hwake hI₁ fun k' hk' r G₂ m₂ hr => h k' (by omega) _ G₂ m₂ ?_
  rcases hr with ⟨⟨j, rfl⟩, hD⟩ | ⟨rfl, hI₂⟩
  · refine .inl ⟨?_, hD⟩
    rcases j with _ | j
    · by_cases hl : live = 0
      · subst hl
        refine .inr ?_
        show Os.negErrno32 Os.Darwin.E.NOENT = _
        decide
      · exact .inl (by simp [Os.Darwin.wakeCode, hl])
    · exact .inl rfl
  · refine .inr ⟨?_, hI₂⟩
    show Os.negErrno32 Os.Darwin.E.INTR = _
    decide

/-- The loop of `DarwinImpl.wake`: the tick (`htick`, paid by the caller at `I`), then
`__ulock_wake` (`ulock_wake_wp`); it repeats after `EINTR`. -/
theorem wake_body {t : ThreadId} {p : Ptr} {all : Bool} {I D : (ThreadId → γ) → Mem → Prop}
    (hword : ∀ G m, I G m → m.wordAt p = true)
    (htick : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ m', I G m' → Q () G m' d) → P.WP t (ConcM.liftMem Zig.tick : ConcM Tgt Unit) Q G m d)
    (hpick : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Nat → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ k, d = k + 1 → ∀ a G₁ m', I G₁ m' → Q a G₁ m' k) →
      P.WP t (Os.pick (fun _ => 2) : ConcM Tgt Nat) Q G m d)
    (hwake : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ k, d = k + 1 → ∀ r G₁ m', ((∃ j, r = some j) ∧ D G₁ m' ∨ r = none ∧ I G₁ m') →
        Q r G₁ m' k) →
      P.WP t (Os.futexWake p false (if all then none else some 1) true :
        ConcM Tgt (Option Nat)) Q G m d)
    (N : Nat) (s : Thread_Futex_DarwinImpl_wakeLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hs : (Zig.Packed.toBits s.local2 =
        (if all then Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Os.Darwin.UL_WAKE_ALL
          else Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO)) ∧ d ≤ N ∧ I G m) :
    P.WP t ((Thread_Futex_DarwinImpl_wake.loop25 p).run s) (fun r G' m' d' =>
      if Thread_Futex_DarwinImpl_wake.again25 r.1 then
        ((Zig.Packed.toBits r.2.local2 =
          (if all then Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Os.Darwin.UL_WAKE_ALL
            else Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO)) ∧ d' ≤ N ∧ I G' m') ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
          (fun (_ : Thread_Futex_DarwinImpl_wakeLocals) => 0) s)
      else r.1 = .ret ∧ d' < N ∧ D G' m') G m d := by
  obtain ⟨hbits, hd, hI⟩ := hs
  unfold Thread_Futex_DarwinImpl_wake.loop25
  rw [StateT.run_bind]
  refine WP.bind ?_
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (htick hI fun m₁ hI₁ => WP.pure' ?_)
  -- the errno of a negative code: `0 - (-EINTR) = 4`, `0 - (-ENOENT) = 2`
  have hsub : ∀ (x y : BitVec 32), Zig.sub true (0 : BitVec 32) x = pure y →
      ∀ {Q' : BitVec 32 → (ThreadId → γ) → Mem → Nat → Prop} {G' : ThreadId → γ}
        {m' : Mem} {n' : Nat}, Q' y G' m' n' →
      P.WP t (ConcM.liftMem (StateT.lift (Zig.sub true (0 : BitVec 32) x)) :
        ConcM Tgt (BitVec 32)) Q' G' m' n' :=
    fun x y hx _ _ _ _ hq => WP.liftMem_pure (by rw [hx]; rfl) rfl hq
  have henum : ∀ (x : c_darwin_E)
      {Q' : c_darwin_E → (ThreadId → γ) → Mem → Nat → Prop} {G' : ThreadId → γ}
        {m' : Mem} {n' : Nat}, Q' x G' m' n' →
      P.WP t (ConcM.liftMem (StateT.lift (Zig.enumOf (some x))) : ConcM Tgt c_darwin_E)
        Q' G' m' n' :=
    fun x _ _ _ _ hq => WP.liftMem_pure rfl rfl hq
  have e4 : ((⟨BitVec.ofInt 16 (Zig.val true 4#32)⟩ : c_darwin_E) == c_darwin_E.INTR) = true := by
    decide
  have e2i : ((⟨BitVec.ofInt 16 (Zig.val true 2#32)⟩ : c_darwin_E) == c_darwin_E.INTR) = false := by
    decide
  have e2f : ((⟨BitVec.ofInt 16 (Zig.val true 2#32)⟩ : c_darwin_E) == c_darwin_E.FAULT) = false := by
    decide
  have e2n : ((⟨BitVec.ofInt 16 (Zig.val true 2#32)⟩ : c_darwin_E) == c_darwin_E.NOENT) = true := by
    decide
  fsym [ulock_wake_wp (P := P) (t := t) (p := p) (all := all) hbits hword hpick hwake,
    hsub _ _ (show Zig.sub true (0 : BitVec 32) 4294967292#32 = pure 4#32 from rfl),
    hsub _ _ (show Zig.sub true (0 : BitVec 32) 4294967294#32 = pure 2#32 from rfl),
    henum, e4, e2i, e2f, e2n,
    Thread_Futex_DarwinImpl_wake.again25]

/-- **`Thread.Futex.wake(p, c)`** (macOS, `c ≠ 0`) at a live word `p`, by a caller that supplies
the steps of its primitive at an invariant `I` of the wake's place: the loop's tick (`htick`,
paid from the caller's part), the oracle stop before each wake (`hpick`) and the OS wake of one
waiter, or of all for `c > 1` (`hwake`: done, `D`, after a wake of some `j` waiters; still at
`I` after a spurious `EINTR`, when std wakes again). -/
theorem wake_wp (hcost : P.cost = none) {t : ThreadId} {p : Ptr} {c : BitVec 32} (hc : c ≠ 0)
    {I D : (ThreadId → γ) → Mem → Prop}
    (hword : ∀ G m, I G m → m.wordAt p = true)
    (htick : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ m', I G m' → Q () G m' d) → P.WP t (ConcM.liftMem Zig.tick : ConcM Tgt Unit) Q G m d)
    (hpick : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Nat → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ k, d = k + 1 → ∀ a G₁ m', I G₁ m' → Q a G₁ m' k) →
      P.WP t (Os.pick (fun _ => 2) : ConcM Tgt Nat) Q G m d)
    (hwake : ∀ {G : ThreadId → γ} {m : Mem} {d : Nat}
      {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}, I G m →
      (∀ k, d = k + 1 → ∀ r G₁ m', ((∃ j, r = some j) ∧ D G₁ m' ∨ r = none ∧ I G₁ m') →
        Q r G₁ m' k) →
      P.WP t (Os.futexWake p false (if Zig.gt false c (1 : BitVec 32) then none else some 1) true :
        ConcM Tgt (Option Nat)) Q G m d)
    {G : ThreadId → γ} {m : Mem} {n : Nat} {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (hI : I G m) (h : ∀ G' m' d', d' < n → D G' m' → Q () G' m' d') :
    P.WP t (Thread_Futex_wake p c) Q G m n := by
  have hc' : (c == (0 : BitVec 32)) = false := beq_false_of_ne hc
  unfold Thread_Futex_wake Thread_Futex_DarwinImpl_wake
  fsym [WP.loop (P := P) (t := t) (Thread_Futex_DarwinImpl_wake.loop25 p)
      Thread_Futex_DarwinImpl_wake.again25
      (fun (s : Thread_Futex_DarwinImpl_wakeLocals) G' m' d' =>
        (Zig.Packed.toBits s.local2 =
          (if Zig.gt false c (1 : BitVec 32) then
            Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Os.Darwin.UL_WAKE_ALL
          else Os.Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO)) ∧ d' ≤ n ∧ I G' m')
      (fun _ => 0)
      (fun r G' m' d' => r.1 = Thread_Futex_DarwinImpl_wakeExit.ret ∧ d' < n ∧ D G' m')
      (wake_body (P := P) (t := t) (p := p) (all := Zig.gt false c (1 : BitVec 32))
        hword htick hpick hwake n),
    ul_bits, hc', h]

end_when

end Futex

end Threadsync
