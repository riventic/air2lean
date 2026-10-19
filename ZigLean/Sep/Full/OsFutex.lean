import ZigLean.Conc.OsRules
import ZigLean.Conc.Logic
import ZigLean.Sep.Full.AutoAttr

/-!
# The OS futex rows in a protocol (premises OSF-01, OSF-02)

The rules of the untimed OS futex wait (`Os.futexWait p e false`), of the OS futex wake
(`Os.futexWake`) and of the rows over them, `os.linux.futex_4arg` (WAIT) and `futex_3arg` (WAKE)
and libc `__ulock_wait2`/`__ulock_wake` (`ZigLean/Os/Futex.lean`), for every protocol
(`Proto.WP`). Std's translated `Thread.Futex` code reaches the kernel's queues only through these
rows once the hand models of `Thread.Futex.wait`/`wake` are deleted (STD-05). The rules of a
lock's, a word's, an event's and a condition's code at the OS wait and wake are next to their
other rules (`LockRules.lean`, `WordRules.lean`, `Event.lean`, `Cond.lean`).

* **Wake.** Every option of an OS wake wakes the same threads as a scheduler wake
  (`Thread.futexWake`, the part of the `wake` sync op) of `wakeSize n k` threads with some choices
  (`Os.wakeAt_futexWake`). So `WP.osFutexWake` asks for what the scheduler's wake asks, at the
  count the OS model wakes: Linux the kernel's `nr_wake` (`Linux.wakeLimit`, at most `2^31 − 1`:
  `Linux.wakeLimit_le`), macOS one waiter, or every waiter with `WAKE_ALL` (`wakeAt_all`).
* **Wait.** `WP.osFutexWait`: a pending interrupt is delivered, the thread stops at the oracle's
  pick, and in the same turn the kernel compares the word (an atomic relaxed read of its newest
  message): `mismatch`, `EINTR`, or the scheduler's `wait`, after which a pending interrupt is
  delivered again.
* **Rows** (`@[fsym]`): `WP.futex_4arg`, `WP.futex_3arg`, `WP.ulock_wait2`, `WP.ulock_wake` reduce
  a row with std's arguments to the generic op, with the row's return code of each result
  (`Linux.waitCode`, `Darwin.waitCode`, `Darwin.wakeCode`).

**The wake count** (audit soundness-2026-10-14 §S5). The scheduler's `wake p n` of the hand
models wakes `min n k` of `k` waiters. Natively std's `wake(p, n)` on macOS sets `WAKE_ALL` for
`n > 1` and wakes all `k` (`wakeAt_all`), and on Linux it clamps `n` to `maxInt(i32)`
(`Linux.wakeLimit_le`). `Thread.wakePick_length` states the hand model's count.
-/

namespace Zig

namespace Thread

/-- A wake of up to `n` of the waiters `l` wakes `min n l.length` of them. -/
theorem wakePick_length : ∀ (n : Nat) (l : List ThreadId) (cs : List Nat),
    (wakePick n l cs).length = Nat.min n l.length
  | 0, _, _ => by simp [wakePick]
  | _ + 1, [], _ => by simp [wakePick]
  | n + 1, w :: ws, cs => by
    simp only [wakePick, List.length_cons]
    rw [wakePick_length, List.length_eraseIdx_of_lt (by simpa using Nat.mod_lt _ (Nat.succ_pos _))]
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.min_def]
    split <;> split <;> omega

/-- A wake at `p` with nobody queued there wakes nobody, whatever its count. -/
theorem futexWake_none {p : Ptr} {m : Mem} (h0 : m.waitersAt p = []) (n n' : Nat)
    (cs : List Nat) : (futexWake p n cs).run m = (futexWake p n' cs).run m := by
  have : ∀ k, wakeSet m.waiters p k cs = #[] := fun k => by
    unfold wakeSet
    have hl : (m.waiters.filter (·.2 == p)).toList.map (·.1) = [] := by
      unfold Mem.waitersAt at h0; rw [Array.toList_filter]; exact h0
    rw [hl]; cases k <;> rfl
  simp only [futexWake, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.run, this]

end Thread

namespace Os

/-- Every sublist of `l` is the result of a wake's picks (`Thread.wakePick`) with some choices. -/
theorem exists_wakePick : ∀ {ys l : List ThreadId}, ys.Sublist l →
    ∃ cs, Thread.wakePick ys.length l cs = ys
  | [], l, _ => ⟨[], by cases l <;> rfl⟩
  | y :: ys, l, h => by
    obtain ⟨r₁, r₂, rfl, hy, hs⟩ := List.cons_sublist_iff.mp h
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
    have hs' : ys.Sublist ((r₁ ++ r₂).eraseIdx i) := by
      rw [List.eraseIdx_append_of_lt_length hi]
      exact hs.trans (List.sublist_append_right _ _)
    obtain ⟨cs, hcs⟩ := exists_wakePick hs'
    refine ⟨i :: cs, ?_⟩
    have hil : i < (r₁ ++ r₂).length := by simp; omega
    match hl : r₁ ++ r₂, hil with
    | w :: ws, hil =>
      rw [hl] at hcs
      have hget : (w :: ws)[i] = y := by
        rw [← hiy]; simp only [← hl]; exact List.getElem_append_left hi
      have hm : i % (ws.length + 1) = i := Nat.mod_eq_of_lt (by simpa using hil)
      simp only [List.length_cons, Thread.wakePick, List.headD_cons, List.tail_cons, hm, hcs,
        hget]

/-- **Every option of an OS wake is a scheduler wake** (`Thread.futexWake`, the `wake` sync op's
part) of `wakeSize n k` threads with some choices `cs`: the OS model wakes the same threads, in
the same order, as the scheduler can. -/
theorem wakeAt_futexWake {c : Nat} {p : Ptr} {n : Option Nat} {m m' : Mem} {j : Nat}
    (h : ((wakeAt c p n).run m).run = some (.ok (some j, m'))) :
    ∃ cs, ((Thread.futexWake p (wakeSize n (m.waitersAt p).length) cs).run m).run =
      some (.ok ((), m')) := by
  unfold wakeAt at h
  cases hs : (wakeSets m p n)[c]? with
  | none => simp [zig_unfold, ExceptT.run, hs] at h
  | some ts =>
    simp [wakeThreads, zig_unfold, ExceptT.run, hs] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨hsub, hlen⟩ := wakeSets_mem (List.mem_of_getElem? hs)
    obtain ⟨cs, hcs⟩ := exists_wakePick hsub
    refine ⟨cs, ?_⟩
    rw [← hlen]
    simp only [Mem.waitersAt] at hcs
    simp [Thread.futexWake, Thread.wakeSet, zig_unfold, ExceptT.run, hcs]

/-- A wake option past the last set (`EINTR` of `__ulock_wake`) wakes nobody. -/
theorem wakeAt_none {c : Nat} {p : Ptr} {n : Option Nat} {m m' : Mem}
    (h : ((wakeAt c p n).run m).run = some (.ok (none, m'))) : m' = m := by
  unfold wakeAt at h
  cases hs : (wakeSets m p n)[c]? with
  | none => simp [zig_unfold, ExceptT.run, hs] at h; exact h.symm
  | some ts => simp [wakeThreads, zig_unfold, ExceptT.run, hs] at h

/-- `wakeAt` never throws. -/
theorem wakeAt_run (c : Nat) (p : Ptr) (n : Option Nat) (m : Mem) :
    ∃ r m', ((wakeAt c p n).run m).run = some (.ok (r, m')) := by
  unfold wakeAt
  cases hs : (wakeSets m p n)[c]? with
  | none => exact ⟨none, m, by simp [zig_unfold, ExceptT.run, hs]⟩
  | some ts => exact ⟨some ts.length, _, by simp [wakeThreads, zig_unfold, ExceptT.run, hs]; rfl⟩

/-- The option of a wake that woke `j` threads woke `wakeSize n k` of the `k` queued ones. -/
theorem wakeAt_some {c : Nat} {p : Ptr} {n : Option Nat} {m m' : Mem} {j : Nat}
    (h : ((wakeAt c p n).run m).run = some (.ok (some j, m'))) :
    j = wakeSize n (m.waitersAt p).length := by
  unfold wakeAt at h
  cases hs : (wakeSets m p n)[c]? with
  | none => simp [zig_unfold, ExceptT.run, hs] at h
  | some ts =>
    simp [wakeThreads, zig_unfold, ExceptT.run, hs] at h
    rw [← h.1]; exact (wakeSets_mem (List.mem_of_getElem? hs)).2

/-- **A wake of every waiter** (`none`: macOS `WAKE_ALL`) that woke `j` threads woke all `k` of
them: nobody is left in the queue at `p`. -/
theorem wakeAt_all {c : Nat} {p : Ptr} {m m' : Mem} {j : Nat}
    (h : ((wakeAt c p none).run m).run = some (.ok (some j, m'))) :
    j = (m.waitersAt p).length ∧ m'.waitersAt p = [] := by
  refine ⟨by rw [wakeAt_some h]; rfl, ?_⟩
  unfold wakeAt at h
  cases hs : (wakeSets m p none)[c]? with
  | none => simp [zig_unfold, ExceptT.run, hs] at h
  | some ts =>
    simp [wakeThreads, zig_unfold, ExceptT.run, hs] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨hsub, hlen⟩ := wakeSets_mem (List.mem_of_getElem? hs)
    have heq : ts = m.waitersAt p :=
      hsub.eq_of_length (by rw [hlen]; rfl)
    unfold Mem.waitersAt
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro w hw hp
    simp only [Array.toList_filter, List.mem_filter, Array.mem_toList_iff] at hw
    have hmem : w.1 ∈ ts := by
      rw [heq]; unfold Mem.waitersAt
      refine List.mem_map.mpr ⟨w, ?_, rfl⟩
      simp only [List.mem_filter, Array.mem_toList_iff]
      exact ⟨hw.1, hp⟩
    have hc := hw.2
    simp [hmem] at hc

/-- A finite wake count covering the queue wakes every waiter at `p`. This counts queue
entries; relating their number to a native-thread bound is a separate validity obligation. -/
theorem wakeAt_all_of_le {c n : Nat} {p : Ptr} {m m' : Mem} {j : Nat}
    (h : ((wakeAt c p (some n)).run m).run = some (.ok (some j, m')))
    (hn : (m.waitersAt p).length ≤ n) :
    j = (m.waitersAt p).length ∧ m'.waitersAt p = [] := by
  have hs : wakeSets m p (some n) = wakeSets m p none := by
    simp [wakeSets, Nat.min_eq_right hn]
  apply wakeAt_all
  simpa only [wakeAt, zig_unfold, ExceptT.run, hs] using h

/-- An OS wake of up to `n ≥ 1` (or all) waiters takes the run of a scheduler wake of at least
one (`WInv.wake`, `FEvent.Inv.wake`, …): with nobody queued, every count wakes nobody. -/
theorem futexWake_pos {p : Ptr} {n : Option Nat} (hn : ∀ k, n = some k → 1 ≤ k) {m m' : Mem}
    {cs : List Nat}
    (h : ((Thread.futexWake p (wakeSize n (m.waitersAt p).length) cs).run m).run =
      some (.ok ((), m'))) :
    ∃ c, 1 ≤ c ∧ ((Thread.futexWake p c cs).run m).run = some (.ok ((), m')) := by
  by_cases h0 : m.waitersAt p = []
  · exact ⟨1, Nat.le_refl _, by rw [← Thread.futexWake_none h0 (wakeSize n _) 1]; exact h⟩
  · refine ⟨_, ?_, h⟩
    have hk : 1 ≤ (m.waitersAt p).length := List.length_pos_iff.mpr h0
    cases n with
    | none => exact hk
    | some k =>
      have := hn k rfl
      simp only [wakeSize, Option.map_some, Option.getD_some, Nat.min_def]
      split <;> omega

/-- `takeInterrupt` delivers the current thread's pending interrupt, if there is one. -/
theorem takeInterrupt_run (m : Mem) :
    ((takeInterrupt.run m).run = some (.ok (m.os.interrupts.contains m.current,
      if m.os.interrupts.contains m.current then
        { m with os := { m.os with interrupts := m.os.interrupts.erase m.current } } else m))) := by
  unfold takeInterrupt
  by_cases h : m.current ∈ m.os.interrupts <;>
    simp [h, zig_unfold, ExceptT.run, set, StateT.set, MonadStateOf.set]

/-- `takeInterrupt` changes at most the OS state. -/
theorem takeInterrupt_os {m m' : Mem} {b : Bool}
    (h : (takeInterrupt.run m).run = some (.ok (b, m'))) : ∃ o, m' = { m with os := o } := by
  rw [takeInterrupt_run] at h; cases h
  split
  · exact ⟨_, rfl⟩
  · exact ⟨m.os, rfl⟩

/-! ## The return codes of the rows -/

namespace Linux

/-- `futex_4arg`'s result for a wait's result (`Linux.futex_4arg`'s match). -/
def waitCode : WaitResult → BitVec 64
  | .woken => 0
  | .mismatch => negErrno E.AGAIN
  | .interrupted => negErrno E.INTR
  | .timedOut => negErrno E.TIMEDOUT

/-- **The Linux wake count is at most `2^31 − 1`** (`nr_wake` is an `int`): every `val`, also
`0xffffffff`, which the kernel reads as `-1` and so wakes one. Std clamps `max_waiters` to
`maxInt(i32)` before the call, so it wakes up to `min(max_waiters, 2^31 − 1)` threads. -/
theorem wakeLimit_le (v : BitVec 32) : wakeLimit v ≤ 2 ^ 31 - 1 := by
  unfold wakeLimit
  split
  · omega
  · rename_i h
    have h1 := BitVec.toInt_eq_toNat_cond v
    have hlt := v.isLt
    split at h1 <;> omega

theorem wakeLimit_pos (v : BitVec 32) : 1 ≤ wakeLimit v := by
  unfold wakeLimit; split
  · exact Nat.le_refl _
  · rename_i h
    have h1 := BitVec.toInt_eq_toNat_cond v
    split at h1 <;> omega

/-- `maxInt(i32)`, std's clamp, is the kernel's count. -/
theorem wakeLimit_maxInt : wakeLimit (BitVec.ofNat 32 (2 ^ 31 - 1)) = 2 ^ 31 - 1 := by decide

end Linux

namespace Darwin

/-- `__ulock_wait2`'s result for a wait's result (`Darwin.ulockWait`'s match). -/
def waitCode : WaitResult → BitVec 32
  | .woken | .mismatch => 0
  | .interrupted => negErrno32 E.INTR
  | .timedOut => negErrno32 E.TIMEDOUT

/-- `__ulock_wake`'s result for a wake's result. -/
def wakeCode : Option Nat → BitVec 32
  | none => negErrno32 E.INTR
  | some 0 => negErrno32 E.NOENT
  | some (_ + 1) => 0

/-- `__ulock_wake`'s waiters: one, or all with `WAKE_ALL`. -/
def wakeMax (op : BitVec 32) : Option Nat :=
  if op = UL_COMPARE_AND_WAIT_NO_ERRNO then some 1 else none

end Darwin

end Os

namespace Conc
namespace Proto

variable {Tgt γ : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}

open Os in
/-- **An OS futex wake** (`Os.futexWake`, OSF-02) by thread `t`: it stops with the ghost value `g`
at the oracle's pick; in the same turn it wakes `wakeSize w k` of the `k` threads queued at `p`,
the same threads as a scheduler wake with some choices `cs` (`wakeAt_futexWake`), or, with
`spurious`, nobody (`EINTR`). -/
theorem WP.osFutexWake {p : Ptr} {w : Option Nat} {spurious : Bool}
    {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      (∀ cs m', ((Thread.futexWake p (wakeSize w (m₁.waitersAt p).length) cs).run
          { m₁ with current := t }).run = some (.ok ((), m')) →
        Q (some (wakeSize w (m₁.waitersAt p).length)) G₁ m' k) ∧
      (spurious = true → Q none G₁ { m₁ with current := t } k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWake p w spurious : ConcM Tgt (Option Nat)) Q G m n := by
  unfold Os.futexWake Os.pick
  refine WP.bind (WP.sync (fun k hk => ?_) hcost)
  obtain ⟨g, hi, hc⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hcr => ?_⟩
  obtain ⟨hw, hsp⟩ := hc G₁ m₁ hg hi₁
  refine WP.liftMem (fun e he => ?_) (fun r m' hr => ?_) fun hn => ?_
  · obtain ⟨r, m', hr⟩ := wakeAt_run c p w { m₁ with current := t }
    rw [hr] at he; cases he
  · cases r with
    | none =>
      have := wakeAt_none hr; subst this
      refine ⟨rfl, hsp ?_⟩
      cases spurious
      · -- without `spurious` every option wakes a set
        exfalso
        unfold wakeAt at hr
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcr
        rcases hcr with hc | ⟨hc0, -⟩
        · simp [zig_unfold, ExceptT.run, wakeThreads, List.getElem?_eq_getElem hc] at hr
        · exact absurd hc0 (Nat.ne_of_gt (wakeCount_pos p w _))
      · rfl
    | some j =>
      have hj := wakeAt_some hr
      obtain ⟨cs, hcs⟩ := wakeAt_futexWake hr
      have hthr : m'.threads = m₁.threads := (wakeAt_frame hr).2.2.2.2
      subst hj
      exact ⟨by rw [hthr], hw cs m' hcs⟩
  · obtain ⟨r, m', hr⟩ := wakeAt_run c p w { m₁ with current := t }
    rw [hr] at hn; cases hn

open Os in
/-- **An untimed OS futex wait** (`Os.futexWait p e false`, OSF-01) by thread `t`. A pending
interrupt is delivered first (the memory `m₀`); the thread stops with the ghost value `g` at
the oracle's pick; in the same turn the kernel reads the word (`futexWord`, an atomic relaxed read
of its newest message, the memory `m₂`): `mismatch` if it is not `e`, else `EINTR`
(`interrupted`) or a sleep at the scheduler's `wait p e`, after which a pending interrupt makes it
`interrupted`, else `woken`. -/
theorem WP.osFutexWait {p : Ptr} {e : BitVec 32}
    {Q : WaitResult → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ b₀ m₀, (Os.takeInterrupt.run m).run = some (.ok (b₀, m₀)) →
      ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m₀ ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      (∀ er, ((futexWord p).run { m₁ with current := t }).run = some (.error er) → P.ErrOk er) ∧
      (((futexWord p).run { m₁ with current := t }).run = none → P.Partial) ∧
      ∀ v m₂, ((futexWord p).run { m₁ with current := t }).run = some (.ok (v, m₂)) →
        m₂.threads.size = m₁.threads.size ∧
        (v ≠ e → Q .mismatch G₁ m₂ k) ∧
        (v = e → Q .interrupted G₁ m₂ k ∧
          ∀ k', k = k' + 1 → ∃ g', P.inv (upd G₁ t g') m₂ ∧ ∀ G₂ m₃, G₂ t = g' → P.inv G₂ m₃ →
            P.Step t (.wait p e) G₂ m₃ fun _ G₄ m₄ =>
              Q (if m₄.os.interrupts.contains m₄.current then .interrupted else .woken) G₄
                (if m₄.os.interrupts.contains m₄.current then
                  { m₄ with os := { m₄.os with interrupts := m₄.os.interrupts.erase m₄.current } }
                  else m₄) k'))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWait p e false : ConcM Tgt WaitResult) Q G m n := by
  unfold Os.futexWait Os.pick
  refine WP.bind (WP.liftMem (fun er he => by rw [takeInterrupt_run] at he; cases he)
    (fun b₀ m₀ h₀ => ⟨?_, ?_⟩) fun hn => by rw [takeInterrupt_run] at hn; cases hn)
  · rw [takeInterrupt_run] at h₀; cases h₀; split <;> rfl
  · refine WP.bind (WP.sync (fun k hk => ?_) hcost)
    obtain ⟨g, hi, hc⟩ := h b₀ m₀ h₀ k hk
    refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hcr => ?_⟩
    obtain ⟨herr, hnone, hk'⟩ := hc G₁ m₁ hg hi₁
    refine WP.bind (WP.liftMem herr (fun v m₂ hr => ?_) hnone)
    obtain ⟨hsz, hne, heq⟩ := hk' v m₂ hr
    refine ⟨hsz, ?_⟩
    by_cases hv : v = e
    · have hcnt := waitCount_eq (timed := false) (hv ▸ hr)
      simp only [hcnt, Bool.false_eq_true, ↓reduceIte] at hcr
      obtain ⟨hint, hw⟩ := heq hv
      simp only [hv, ne_eq, not_true_eq_false, ↓reduceIte]
      rcases hcr with hc | ⟨hc, -⟩
      · match c, hc with
        | 0, _ =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine WP.bind (WP.sync (fun k' hk'' => ?_) hcost)
          obtain ⟨g', hi', hs⟩ := hw k' hk''
          refine ⟨g', hi', fun G₂ m₃ hg' hi₂ => Step.mono P ?_ (hs G₂ m₃ hg' hi₂)⟩
          intro _ G₄ m₄ hq
          refine WP.bind (WP.liftMem (fun er he => by rw [takeInterrupt_run] at he; cases he)
            (fun b m₅ h₅ => ?_) fun hn => by rw [takeInterrupt_run] at hn; cases hn)
          rw [takeInterrupt_run] at h₅; cases h₅
          exact ⟨by split <;> rfl, WP.pure' hq⟩
        | 1, _ => exact WP.pure' hint
      · cases hc
    · simp only [hv, ne_eq, not_false_eq_true, ↓reduceIte]
      exact WP.pure' (hne hv)

/-! ## The rows with std's arguments (`@[fsym]`) -/

open Os

/-- `os.linux.futex_4arg(uaddr, .{ .cmd = .WAIT, .private = _ }, val, null)` (OSF-01, std's
untimed `Thread.Futex.wait` on Linux): the untimed OS wait, with `futex_4arg`'s return code. -/
@[fsym] theorem WP.futex_4arg {p : Ptr} {op e : BitVec 32}
    (hop : op = Linux.FUTEX_WAIT ∨ op = Linux.FUTEX_WAIT ||| Linux.FUTEX_PRIVATE)
    {Q : BitVec 64 → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t (Os.futexWait p e false : ConcM Tgt WaitResult)
      (fun r => Q (Linux.waitCode r)) G m n) :
    P.WP t (Linux.futex_4arg p op e none : ConcM Tgt (BitVec 64)) Q G m n := by
  have hc : ¬ (op ≠ Linux.FUTEX_WAIT ∧ op ≠ Linux.FUTEX_WAIT ||| Linux.FUTEX_PRIVATE) :=
    fun ⟨h1, h2⟩ => hop.elim h1 h2
  unfold Linux.futex_4arg
  simp only [hc, ↓reduceIte, Option.isSome_none]
  refine WP.bind (WP.mono (fun r _ _ _ hq => ?_) h)
  cases r <;> exact WP.pure' hq

/-- `os.linux.futex_3arg(uaddr, .{ .cmd = .WAKE, .private = _ }, val)` (OSF-02, std's
`Thread.Futex.wake` on Linux): the OS wake of up to `wakeLimit val` waiters, with the number
woken. -/
@[fsym] theorem WP.futex_3arg {p : Ptr} {op v : BitVec 32}
    (hop : op = Linux.FUTEX_WAKE ∨ op = Linux.FUTEX_WAKE ||| Linux.FUTEX_PRIVATE)
    {Q : BitVec 64 → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t (Os.futexWake p (some (Linux.wakeLimit v)) false : ConcM Tgt (Option Nat))
      (fun r => Q (BitVec.ofNat 64 (r.getD 0))) G m n) :
    P.WP t (Linux.futex_3arg p op v : ConcM Tgt (BitVec 64)) Q G m n := by
  have hc : ¬ (op ≠ Linux.FUTEX_WAKE ∧ op ≠ Linux.FUTEX_WAKE ||| Linux.FUTEX_PRIVATE) :=
    fun ⟨h1, h2⟩ => hop.elim h1 h2
  unfold Linux.futex_3arg
  simp only [hc, ↓reduceIte]
  exact WP.bind (WP.mono (fun r _ _ _ hq => WP.pure' hq) h)

/-- libc `__ulock_wait2(UL{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true }, ptr, val, 0, 0)` (OSF-01,
std's untimed `Thread.Futex.wait` on macOS): the untimed OS wait, with `__ulock_wait2`'s return
code. -/
@[fsym] theorem WP.ulock_wait2 {op : BitVec 32} {p : Ptr} {v : BitVec 64}
    (hop : op = Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO) (hv : v.toNat < 2 ^ 32)
    {Q : BitVec 32 → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t (Os.futexWait p (v.setWidth 32) false : ConcM Tgt WaitResult)
      (fun r => Q (Darwin.waitCode r)) G m n) :
    P.WP t (Darwin.__ulock_wait2 op (some p) v 0 0 : ConcM Tgt (BitVec 32)) Q G m n := by
  unfold Darwin.__ulock_wait2 Darwin.ulockWait
  have hc : ¬ (op ≠ Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ∨ 2 ^ 32 ≤ v.toNat) := by
    rintro (h1 | h2)
    · exact h1 hop
    · omega
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hc]
  refine WP.bind (WP.mono (fun r _ _ _ hq => ?_) h)
  cases r <;> exact WP.pure' hq

/-- libc `__ulock_wake(UL{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true, .WAKE_ALL = _ }, ptr, 0)`
(OSF-02, std's `Thread.Futex.wake` on macOS, which sets `WAKE_ALL` for more than one waiter): the
OS wake of one waiter or of all, with a spurious `EINTR`. -/
@[fsym] theorem WP.ulock_wake {op : BitVec 32} {p : Ptr}
    (hop : op = Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ∨
      op = Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Darwin.UL_WAKE_ALL)
    {Q : BitVec 32 → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t (Os.futexWake p (Darwin.wakeMax op) true : ConcM Tgt (Option Nat))
      (fun r => Q (Darwin.wakeCode r)) G m n) :
    P.WP t (Darwin.__ulock_wake op (some p) 0 : ConcM Tgt (BitVec 32)) Q G m n := by
  unfold Darwin.__ulock_wake
  have hc : ¬ ((op ≠ Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ∧
      op ≠ Darwin.UL_COMPARE_AND_WAIT_NO_ERRNO ||| Darwin.UL_WAKE_ALL) ∨ (0 : BitVec 64) ≠ 0) :=
    fun h => h.elim (fun ⟨h1, h2⟩ => hop.elim h1 h2) (· rfl)
  simp only [hc, ↓reduceIte]
  refine WP.bind (WP.mono (fun r _ _ _ hq => ?_) h)
  rcases r with _ | _ | j <;> exact WP.pure' hq

end Proto
end Conc
end Zig
