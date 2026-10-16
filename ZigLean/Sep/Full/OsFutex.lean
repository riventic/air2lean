import ZigLean.Sep.Full.LockRules
import ZigLean.Conc.OsRules

/-!
# The OS futex rows in a protocol (premises OSF-01, OSF-02; STD-05 step A, WIP)

The rules of the untimed OS futex wait (`Os.futexWait p e false`) and of the OS futex wake
(`Os.futexWake`), the models under `os.linux.futex_4arg`/`futex_3arg` and libc
`__ulock_wait2`/`__ulock_wake` (`ZigLean/Os/Futex.lean`). Std's translated `Thread.Futex` code calls
them once the hand models of `Thread.Futex.wait`/`wake` are deleted (STD-05).

* **Wake.** Every option of an OS wake wakes the same threads as a scheduler wake
  (`Thread.futexWake`, the part of the `wake` sync op) of `wakeSize n k` threads with some choices
  (`Os.wakeAt_futexWake`). So `WP.osFutexWake` asks for what the scheduler's wake asks, at the
  count the OS model wakes (Linux: the kernel's `nr_wake`, which std clamps to `maxInt(i32)`;
  macOS: one waiter, or every waiter with `WAKE_ALL`).
* **Wait.** `WP.osFutexWait`: a pending interrupt is delivered, the thread stops at the oracle's
  pick, and in the same turn the kernel compares the word (an atomic relaxed read of its newest
  message): `mismatch`, `EINTR`, or the scheduler's `wait`.
* **A lock's word** (`FLock.wp_osWait`): the thread is at `spin` at the pick and the compare, and
  goes to `wait` only when it sleeps, in the same turn. At the pick the protocol knows nothing
  about the queue (a timed waiter is runnable while it is queued, so no global fact says that a
  resumed thread is not queued); `spin` is not a queue place (`LockWord.Queue`), so the rules of
  the scheduler's wait (`WInv.wait`, `WInv.spurious`) get their premise from the `wait` stop.
-/

namespace Zig
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

/-- `takeInterrupt` delivers the current thread's pending interrupt, if there is one. -/
theorem takeInterrupt_run (m : Mem) :
    ((takeInterrupt.run m).run = some (.ok (m.os.interrupts.contains m.current,
      if m.os.interrupts.contains m.current then
        { m with os := { m.os with interrupts := m.os.interrupts.erase m.current } } else m))) := by
  unfold takeInterrupt
  by_cases h : m.current ∈ m.os.interrupts <;>
    simp [h, zig_unfold, ExceptT.run, set, StateT.set, MonadStateOf.set]

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

end Proto
end Conc

namespace Full
namespace FLock

open Conc Proto LockWord

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- The same memory, but the OS state. -/
theorem _root_.Zig.Full.LockWord.WInv.osState {L : LockWord} {Pl : ThreadId → LPh} {m : Mem}
    (hi : L.WInv Pl m) (o : OsState) : L.WInv Pl { m with os := o } :=
  ⟨hi.csize, hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, hi.wfp,
    hi.rel, hi.fq, hi.wit, hi.owner⟩

/-- A change of the OS state only (`takeInterrupt`) keeps the protocol's invariant. -/
theorem Fits.osState (hP : L.Fits K P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    (hi : P.inv G m) (hok : ok (G t)) (hng : L.ph (G t) ≠ .gone) (o : OsState) :
    P.inv G { m with os := o } := by
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi
  have hst : L.Step t m { m with os := o } :=
    Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)
  exact hP.stay hU hok hng hst (hiL.lstay hst (hiL.w.osState o))

/-- `takeInterrupt` keeps the protocol's invariant. -/
theorem Fits.takeInterrupt (hP : L.Fits K P U ok) {G : ThreadId → γ} {m m' : Mem} {t : ThreadId}
    {b : Bool} (hi : P.inv G m) (hok : ok (G t)) (hng : L.ph (G t) ≠ .gone)
    (h : (Os.takeInterrupt.run m).run = some (.ok (b, m'))) :
    P.inv G m' ∧ m'.current = m.current ∧ m'.threads = m.threads := by
  rw [Os.takeInterrupt_run] at h; cases h
  split
  · exact ⟨hP.osState hi hok hng _, rfl, rfl⟩
  · exact ⟨hi, rfl, rfl⟩

/-- **The untimed OS futex wait for `c` at the lock's word** (`Os.futexWait`, OSF-01), by thread
`t` at `spin` (`g`): it goes on at `spin` with a result other than `timedOut`. The thread stays at
`spin` over the oracle's pick and the kernel's compare (an atomic relaxed read: `WInv.load`); it
goes to `wait` only when it sleeps, in the same turn, and the sleep is the scheduler's wait
(`WInv.wait`, `WInv.spurious`). -/
theorem wp_osWait (hP : L.Fits K P U ok) {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}
    {g : γ} (hg : L.ph g = .spin) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Os.WaitResult → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ d, d < n → ∀ r G₁ m', m'.current = t → r ≠ .timedOut → P.inv (upd G₁ t g) m' →
      Q r G₁ m' d)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWait L.ptr (BitVec.ofNat 32 L.c) false : ConcM Tgt Os.WaitResult) Q G m n := by
  have hng : L.ph g ≠ .gone := by rw [hg]; decide
  have hgw : L.ph (L.set g .wait rnil) = .wait := L.ph_set _ _ _
  have hokw : ok (L.set g .wait rnil) := (hP.ok_set _ _ _).mpr hok
  -- `t` holds nothing at `spin`, so `g` is `g` with the place `spin`
  have hgs : L.set (L.set g .wait rnil) .spin rnil = g := by
    obtain ⟨rX₀, hiL₀, -⟩ := (hP.inv _ _).mp hi
    have hheld : L.held g = rnil := by
      have := hiL₀.idle t (by rw [upd_self, hg]; decide); rwa [upd_self] at this
    rw [L.set_set, ← hg, ← hheld, L.set_self]
  refine WP.osFutexWait fun b₀ m₀ h₀ k hk => ⟨g, ?_, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  · exact (hP.takeInterrupt hi (by rw [upd_self]; exact hok) (by rw [upd_self]; exact hng) h₀).1
  -- at the pick: `t` at `spin`
  have hng₁ : L.ph (G₁ t) ≠ .gone := by rw [hg₁]; exact hng
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  obtain ⟨rX, hiL, hU, -⟩ := hP.cur t hi₁ hng₁
  have hU' := hP.curU t hU hng₁
  have ht : t < m₁.threads.size := (hiL.ht hng₁).1
  have hpl : L.pl G₁ t ≠ .gone := hng₁
  refine ⟨fun er he => absurd he (hiL.w.load_noErr (c := 0) (ord := .relaxed) ht hpl
      (by by_cases h0 : loadCount 32 .relaxed 4 L.ptr { m₁ with current := t } = 0
          · exact .inr ⟨h0, rfl⟩
          · exact .inl (Nat.pos_of_ne_zero h0)) er),
    fun _ => .inr hcost, fun v m₂ hr => ?_⟩
  obtain ⟨hst, hcu, hl⟩ := hiL.w.load rfl ht rfl hr
  have hi₂ : P.inv (upd G₁ t g) m₂ := by
    rw [← hg₁, upd_same]; exact hP.stay hU' hok₁ hng₁ hst (hiL.lstay hst hl)
  refine ⟨by rw [hst.threads], fun _ => h k (by omega) _ G₁ m₂ hcu (by decide) hi₂,
    fun _ => ⟨h k (by omega) _ G₁ m₂ hcu (by decide) hi₂, fun k' hk' => ?_⟩⟩
  -- the sleep: `t` goes to `wait`, then the scheduler's wait
  refine ⟨L.set g .wait rnil, hP.toWait hok hg hi₂, fun G₂ m₃ hg₂ hi₃ => ?_⟩
  obtain ⟨rY, hiL₃, hU₃⟩ := (hP.inv _ _).mp hi₃
  have hph : L.pl G₂ t = .wait := by show L.ph (G₂ t) = _; rw [hg₂, hgw]
  have hok₃ : ok (G₂ t) := by rw [hg₂]; exact hokw
  have hng₃ : L.ph (G₂ t) ≠ .gone := by rw [hg₂, hgw]; decide
  have hwo := hiL₃.w.wait_ok (e := BitVec.ofNat 32 L.c) (hiL₃.ht hng₃).1 hng₃
  -- after the wait, at `spin`: the interrupt check keeps the invariant
  have hend : ∀ m₄, m₄.current = t → P.inv (upd G₂ t g) m₄ →
      Q (if m₄.os.interrupts.contains m₄.current then .interrupted else .woken) G₂
        (if m₄.os.interrupts.contains m₄.current then
          { m₄ with os := { m₄.os with interrupts := m₄.os.interrupts.erase m₄.current } }
          else m₄) k' := fun m₄ hc₄ hi₄ => by
    have hok' : ok (upd G₂ t g t) := by rw [upd_self]; exact hok
    have hng' : L.ph (upd G₂ t g t) ≠ .gone := by rw [upd_self]; exact hng
    split
    · exact h k' (by omega) _ G₂ _ hc₄ (by decide) (hP.osState hi₄ hok' hng' _)
    · exact h k' (by omega) _ G₂ _ hc₄ (by decide) hi₄
  refine ⟨fun _ => hP.live hiL₃ (by rw [hg₂]; exact hgw), fun hq => ⟨fun _ => hwo,
    fun _ he => Zig.Conc.Proto.noErr_of_ok hwo he, fun b m' hw => ?_⟩⟩
  obtain ⟨hst, hb⟩ := hiL₃.w.wait hph hq hw
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
    have := hP.stepAt hg₂ hokw (by rw [hgw]; decide) (by rw [hgw]; decide) (by decide) hiL₃ hU₃
      hst hb.2
    rw [hgs] at this
    exact hend m' hb.1 this
  · simp only [↓reduceIte] at hb ⊢
    obtain ⟨hst', hcu', hl'⟩ := hiL₃.w.spurious hph hq
    have := hP.stepAt hg₂ hokw (by rw [hgw]; decide) (by rw [hgw]; decide) (by decide) hiL₃ hU₃
      hst' hl'
    rw [hgs] at this
    exact ⟨hP.stay hU₃ hok₃ hng₃ hst (hiL₃.lstay hst hb), hend _ hcu' this⟩

end FLock
end Full
end Zig
