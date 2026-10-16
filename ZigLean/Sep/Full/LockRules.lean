import ZigLean.Sep.Full.Lock
import ZigLean.Sep.Full.OsFutex

/-!
# The rules of a lock's code, over full-state resources

The steps of `Io.Mutex`'s code (`lock`, `unlock`; translated from Zig 0.16.0's std code) and of
`Thread.Mutex`'s code (0.15.2: `FutexImpl` on Linux, `os_unfair_lock` on macOS) on the word of a
lock `L : FLock γ` (`ZigLean/Sep/Full/Lock.lean`), proved once for every protocol that has the
lock (`FLock.Fits`, with any primitive next to it). Each rule is a stop (the pick of the op, or the futex op) and
then the op; it gives the protocol's invariant with the thread's new place. The word's part of
each op is `ZigLean/Sep/Full/LockWord.lean` (`WInv.cas`, `WInv.xchgLock`, …); the resource moves
with `Inv.acq` (into the acquiring thread's part) and `Inv.rel` (back into the rest).

| Rule | Op | Place before | Place after |
|---|---|---|---|
| `wp_cas` | `cmpxchg(0 → 1)`, acquire | `out` | `holds` (with the resource), `spin` (read `1`), `wait` (read `c`) |
| `wp_orLock` | `or(1)`, acquire (`c = 3`) | `out` | `holds` (read `0`), or `spin` (read `1` or `3`) |
| `wp_casWeakLock` | weak `cmpxchg(0 → 1)`, acquire (off x86) | `out` | `holds`, or `spin` (any failure) |
| `wp_loadLock` | load, relaxed | any but `gone` | the same |
| `Fits.toWait` | (no op) | `spin` | `wait` |
| `wp_xchgLock` | `xchg(c)`, acquire | `spin` | `holds` (read `0`), or `wait` |
| `wp_wait`, `wp_waitD` | futex wait for `c` | `wait` | `spin` |
| `wp_xchgUnlock` | `xchg(0)`, release | `holds` | `out` (read `1`), or `wake` (read `c`); the lock gets the resource |
| `wp_xchgRel` | `xchg(0)`, release (`c = 1`) | `holds` | `wake` |
| `wp_casD` | `cmpxchg(0 → 1)`, acquire (`c = 1`) | `out` or `spin` | `holds`, or `wait` |
| `wp_wake` | futex wake of 1 | `wake` | `out` |
| `wp_osWait` | OS futex wait for `c` (`Os.futexWait`, OSF-01) | `spin` | `spin` |
| `wp_osWake` | OS futex wake of `w ≥ 1` or all (`Os.futexWake`, OSF-02) | `wake` | `out`, or `wake` (spurious `EINTR`) |
-/

namespace Zig
namespace Full

open FAssn Conc Proto LockWord

namespace FLock

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## A protocol with the lock -/

/-- If every thread has ended, sleeps at a futex or waits at a join, no thread waits at the
word. -/
theorem Fits.noWaits (hP : L.Fits K P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem}
    (hi : L.Inv G rX m)
    (hall : ∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) :
    ¬ L.Waits m.waiters := fun hp => by
  obtain ⟨v, hv, hq, hb, -⟩ := hi.w.wit hp
  rcases hall v hv with h | h | h
  · have := hP.fin _ h; simp only [pl] at hb; rw [this] at hb; cases hb
  · rw [hq] at h; cases h
  · have := hP.joins _ h; simp only [pl] at hb; rw [this] at hb; cases hb

/-- A thread at `lock`'s futex wait is not the last one (`Fits.noWaits`). -/
theorem Fits.live (hP : L.Fits K P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem}
    (hi : L.Inv G rX m) {t : ThreadId} (ht : L.ph (G t) = .wait) : P.Live t G m := by
  intro hw hall
  apply hP.noWaits hi hall
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hw
  have he : (m.waiters[i]).1 = t := by simpa using he
  rcases hi.w.fq _ (Array.getElem_mem hi') with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Array.any_eq_true.mpr ⟨i, hi', by simp [h1]⟩
  · simp only [pl] at h2; rw [he, ht] at h2; cases h2

/-- A lock step with `t`'s new place and resource keeps the protocol's invariant. -/
theorem Fits.step (hP : L.Fits K P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {p : LPh} {h : Res} (hU : U G rX m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone)
    (hs : L.Step t m m') (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!))
    (hl : L.Inv (upd G t (L.set (G t) p h)) rX m') : P.inv (upd G t (L.set (G t) p h)) m' :=
  (hP.inv _ _).mpr ⟨rX, hl, hP.stable G rX m m' t p h hok hph hU hs hrel⟩

/-- A lock step with the same ghost values keeps the protocol's invariant. -/
theorem Fits.stay (hP : L.Fits K P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} (hU : U G rX m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone)
    (hs : L.Step t m m') (hl : L.Inv G rX m') : P.inv G m' := by
  have := hP.step (p := L.ph (G t)) (h := L.held (G t)) hU hok hph hs (fun h1 h2 => absurd h1 h2)
    (by rw [upd_set_self]; exact hl)
  rwa [upd_set_self] at this

/-- The lock's invariant at a stop of `t` (`current := t`). -/
theorem Inv.cur {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m) (t : ThreadId) :
    L.Inv G rX { m with current := t } :=
  hi.lstay (t := t) (Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)) (hi.w.current t)

/-- The protocol's invariant at a stop of `t`: the same, with `current := t`. -/
theorem Fits.cur (hP : L.Fits K P U ok) {G : ThreadId → γ} {m : Mem} (t : ThreadId)
    (hi : P.inv G m) (hph : L.ph (G t) ≠ .gone) :
    ∃ rX, L.Inv G rX { m with current := t } ∧ U G rX m ∧ P.inv G { m with current := t } := by
  obtain ⟨rX, hiL, hU⟩ := (hP.inv G m).mp hi
  exact ⟨rX, hiL.cur t, hU, (hP.inv _ _).mpr ⟨rX, hiL.cur t, hP.atStop G rX m t hph hU⟩⟩

/-- `U` at a stop of `t`. -/
theorem Fits.curU (hP : L.Fits K P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem} (t : ThreadId)
    (hU : U G rX m) (hph : L.ph (G t) ≠ .gone) : U G rX { m with current := t } :=
  hP.atStop G rX m t hph hU

/-! ## The ops in generated code (`WP`) -/

variable {σ α : Type} [Packed α 32]

/-- The common shape of an op's rule: a pick, then a `MemM` op of `t` from the invariant at the
stop. -/
theorem Fits.pick {count : Mem → Nat} {x : Nat → MemM β} (hP : L.Fits K P U ok) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : β × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hnoErr : ∀ (G₁ : ThreadId → γ) (rX : Res) (m₁ : Mem) (c : Nat), G₁ t = g → L.Inv G₁ rX { m₁ with current := t } →
      (c < count { m₁ with current := t } ∨ count { m₁ with current := t } = 0 ∧ c = 0) →
      ∀ e, ((x c).run { m₁ with current := t }).run ≠ some (.error e))
    (h : ∀ k, n = k + 1 → ∀ (G₁ : ThreadId → γ) (rX : Res) (m₁ : Mem) (c : Nat) (r : β) (m' : Mem), G₁ t = g → L.Inv G₁ rX { m₁ with current := t } →
      U G₁ rX { m₁ with current := t } →
      ((x c).run { m₁ with current := t }).run = some (.ok (r, m')) → m'.threads = m₁.threads ∧
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((do let c ← (pickC count : CM Tgt σ Nat); callMC (x c)).run s) Q G m n := by
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone₁ : L.ph (G₁ t) ≠ .gone := by rw [hg₁]; exact hgone
  obtain ⟨rX, hiL, hU, -⟩ := hP.cur t hi₁ hgone₁
  have hU' := hP.curU t hU hgone₁
  refine WP.callMC (fun e he => (hnoErr G₁ rX m₁ c hg₁ hiL hcr e he).elim) fun r m' hr => ?_
  obtain ⟨h1, h2⟩ := h k hk G₁ rX m₁ c r m' hg₁ hiL hU' hr
  exact ⟨by rw [h1], h2⟩

/-- `lock`'s first try, `cmpxchg(unlocked → locked_once)`, by thread `t` at `out` (`g`). -/
theorem wp_casOn (hP : L.Fits K P U ok) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r = some S.one ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m') ∨
       (r = some S.two ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgAsC .acquire .relaxed 4 L.ptr S.unl S.one : CM Tgt σ (Option α)).run s)
      Q G m n := by
  unfold cmpxchgAsC
  refine hP.pick (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.cas_noErr S hS
      ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .out := by simp only [pl]; rw [hg₁, hg]
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hng : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hnh : L.ph (G₁ t) ≠ .holds := by rw [hg₁, hg]; decide
  obtain ⟨hst, hcu, hcase⟩ := hiL.w.cas S hS hph rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  have hrel : L.ph (G₁ t) = .holds → ∀ p : LPh, p ≠ .holds →
      L.Before m' (({ m₁ with current := t } : Mem).clocks[t]!) := fun h => absurd h hnh
  rcases hcase with ⟨rfl, hF, hw, hacq⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · obtain ⟨rL, -, hl⟩ := hiL.acq hst hnh hng hF hacq hw
    refine .inl ⟨rfl, rL, ?_⟩
    have := hP.step hU hok₁ hng hst (fun h' => hrel h' _) hl
    rwa [hg₁] at this
  · refine .inr (.inl ⟨rfl, ?_⟩)
    have := hP.step hU hok₁ hng hst (fun h' => hrel h' _) (hiL.lstepAt hst hnh hng (by decide) hw)
    rwa [hg₁] at this
  · refine .inr (.inr ⟨rfl, ?_⟩)
    have := hP.step hU hok₁ hng hst (fun h' => hrel h' _) (hiL.lstepAt hst hnh hng (by decide) hw)
    rwa [hg₁] at this

/-- A lock step of `t` (not the holder) to a place `p ≠ holds`, as the protocol's invariant. -/
theorem Fits.stepAt (hP : L.Fits K P U ok) {G₁ : ThreadId → γ} {rX : Res} {m₁ m' : Mem}
    {t : ThreadId} {g : γ} {p : LPh} (hg₁ : G₁ t = g) (hok : ok g) (hng : L.ph g ≠ .gone)
    (hnh : L.ph g ≠ .holds) (hp : p ≠ .holds) (hiL : L.Inv G₁ rX m₁) (hU : U G₁ rX m₁)
    (hst : L.Step t m₁ m') (hw : L.WInv (upd (L.pl G₁) t p) m') :
    P.inv (upd G₁ t (L.set g p rnil)) m' := by
  subst hg₁
  exact hP.step hU hok hng hst (fun h => absurd h hnh) (hiL.lstepAt hst hnh hng hp hw)

/-- An acquire of `t` as the protocol's invariant. -/
theorem Fits.stepAcq (hP : L.Fits K P U ok) {G₁ : ThreadId → γ} {rX : Res} {m₁ m' : Mem}
    {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hok : ok g) (hng : L.ph g ≠ .gone)
    (hnh : L.ph g ≠ .holds) (hiL : L.Inv G₁ rX m₁) (hU : U G₁ rX m₁)
    (hst : L.Step t m₁ m') (hF : L.Free G₁) (hacq : L.Acq (L.pl G₁) t m₁ m')
    (hw : L.WInv (upd (L.pl G₁) t .holds) m') :
    ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m' := by
  subst hg₁
  obtain ⟨rL, -, hl⟩ := hiL.acq hst hnh hng hF hacq hw
  exact ⟨rL, hP.step hU hok hng hst (fun h => absurd h hnh) hl⟩

/-- A release of the holder `t` as the protocol's invariant. -/
theorem Fits.stepRel (hP : L.Fits K P U ok) {G₁ : ThreadId → γ} {rX : Res} {m₁ m' : Mem}
    {t : ThreadId} {g : γ} {p : LPh} (hg₁ : G₁ t = g) (hok : ok g) (hph : L.ph g = .holds)
    (hp : p ≠ .holds) (hiL : L.Inv G₁ rX m₁) (hU : U G₁ rX m₁) (hst : L.Step t m₁ m')
    (hbf : L.Before m' (m₁.clocks[t]!)) (hrel : L.Rel t (upd (L.pl G₁) t p) m₁ m')
    (hw : L.WInv (upd (L.pl G₁) t p) m') :
    P.inv (upd G₁ t (L.set g p rnil)) m' := by
  subst hg₁
  exact hP.step hU hok (by rw [hph]; decide) hst (fun _ _ => hbf) (hiL.rel hst hph hp hrel hw)

/-- `lock`'s loop, `xchg(contended)`, by thread `t` at `spin` (`g`). -/
theorem wp_xchgLockOn (hP : L.Fits K P U ok) (S : States α) (hS : S.c = L.c) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .spin)
    (hok : ok g) (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.unl ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r ≠ S.unl ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .xchg .acquire 4 L.ptr S.two : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  refine hP.pick (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.xchg_noErr S hS
      ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .spin := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hcase⟩ := hiL.w.xchgLock S hS hph rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rcases hcase with ⟨hr', hF, hw, hacq⟩ | ⟨hr', hw⟩
  · exact .inl ⟨hr', hP.stepAcq hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) hiL hU hst hF hacq hw⟩
  · exact .inr ⟨hr', hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide) hiL hU hst hw⟩

/-- `unlock`'s `xchg(unlocked)`, by the holder `t` (`g`). -/
theorem wp_xchgUnlockOn (hP : L.Fits K P U ok) (S : States α) (hS : S.c = L.c) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds)
    (hok : ok g) (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.one ∧ P.inv (upd G₁ t (L.set g .out rnil)) m') ∨
       (r = S.two ∧ P.inv (upd G₁ t (L.set g .wake rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .xchg .release 4 L.ptr S.unl : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  refine hP.pick (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.xchg_noErr S hS
      ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .holds := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hbf, hcase⟩ := hiL.w.xchgUnlock S hS hph rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rcases hcase with ⟨hr', hw, hrel⟩ | ⟨hr', hw, hrel⟩
  · exact .inl ⟨hr', hP.stepRel hg₁ hok hg (by decide) hiL hU hst hbf hrel hw⟩
  · exact .inr ⟨hr', hP.stepRel hg₁ hok hg (by decide) hiL hU hst hbf hrel hw⟩

/-- The futex wait at the word for `c`, by thread `t` at `wait` (`g`): it goes on at `spin`. -/
theorem wp_futexWaitOn (hP : L.Fits K P U ok) {ε : Type} {w : Nat} [Packed ε w] {io : Io}
    {e : ε} (he : (Packed.toBits e).setWidth 32 = BitVec.ofNat 32 L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io L.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWaitC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  simp only [he]
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  have hph : L.pl G₁ t = .wait := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hng : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hwo := hiL.w.wait_ok (e := BitVec.ofNat 32 L.c) (hiL.ht hng).1 hng
  refine ⟨fun _ => hP.live hiL (by rw [hg₁]; exact hg), fun hq => ⟨fun _ => hwo,
    fun _ he => Zig.Conc.Proto.noErr_of_ok hwo he, fun b m' hw => ?_⟩⟩
  obtain ⟨hst, hb⟩ := hiL.w.wait hph hq hw
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
    exact h k hk G₁ m' hb.1
      (hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide) hiL hU hst hb.2)
  · simp only [↓reduceIte] at hb ⊢
    obtain ⟨hst', hcu', hl'⟩ := hiL.w.spurious hph hq
    exact ⟨hP.stay hU hok₁ hng hst (hiL.lstay hst hb),
      h k hk G₁ _ hcu'
        (hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide) hiL hU hst' hl')⟩

/-- `lock`'s futex wait for `contended`, by thread `t` at `wait` (`g`): it goes on at `spin`. -/
theorem wp_waitOn (hP : L.Fits K P U ok) (S : States α) (hS : S.c = L.c) {io : Io} {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait)
    (hok : ok g) (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io L.ptr S.two : CM Tgt σ Unit).run s) Q G m n :=
  wp_futexWaitOn hP (by rw [S.bits2, hS]; rfl) hg hok hi h

/-- `unlock`'s futex wake of one waiter, by thread `t` at `wake` (`g`): it goes on at `out`. -/
theorem wp_wakeOn (hP : L.Fits K P U ok) {io : Io} {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wake) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .out rnil)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io L.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWakeC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ cs m' hw => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  have hph : L.pl G₁ t = .wake := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hl⟩ := hiL.w.wake hph (by decide) hw
  exact h k hk G₁ m' hcu
    (hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide) hiL hU hst hl)

/-! ### `ok = True`: every thread runs the lock's code -/

theorem wp_cas (hP : L.Fits K P U fun _ => True) (S : States α) (hS : S.c = L.c) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out)
    (hi : P.inv (upd G t g) m)
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r = some S.one ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m') ∨
       (r = some S.two ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgAsC .acquire .relaxed 4 L.ptr S.unl S.one : CM Tgt σ (Option α)).run s)
      Q G m n := wp_casOn hP S hS hg trivial hi h

theorem wp_xchgLock (hP : L.Fits K P U fun _ => True) (S : States α) (hS : S.c = L.c) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .spin)
    (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.unl ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r ≠ S.unl ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .xchg .acquire 4 L.ptr S.two : CM Tgt σ α).run s) Q G m n :=
  wp_xchgLockOn hP S hS hg trivial hi h

theorem wp_xchgUnlock (hP : L.Fits K P U fun _ => True) (S : States α) (hS : S.c = L.c)
    {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}
    (hg : L.ph g = .holds)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.one ∧ P.inv (upd G₁ t (L.set g .out rnil)) m') ∨
       (r = S.two ∧ P.inv (upd G₁ t (L.set g .wake rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .xchg .release 4 L.ptr S.unl : CM Tgt σ α).run s) Q G m n :=
  wp_xchgUnlockOn hP S hS hg trivial hi h

theorem wp_wait (hP : L.Fits K P U fun _ => True) (S : States α) (hS : S.c = L.c) {io : Io}
    {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io L.ptr S.two : CM Tgt σ Unit).run s) Q G m n :=
  wp_waitOn hP S hS hg trivial hi h

theorem wp_wake (hP : L.Fits K P U fun _ => True) {io : Io} {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wake)
    (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .out rnil)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io L.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n :=
  wp_wakeOn hP hg trivial hi h

/-! ### `Thread.Mutex` (0.15.2): the ops on bits

Stated for any `ok` (a thread with `ok` runs the lock's code), as `MutexImpl` quantifies over it;
`ok = True` gives them with `trivial`. -/

/-- A thread at `spin` (`g`) goes to the futex wait: no memory step. -/
theorem Fits.toWait (hP : L.Fits K P U ok) {t : ThreadId} {G : ThreadId → γ} {m : Mem} {g : γ}
    (hok : ok g) (hg : L.ph g = .spin) (hi : P.inv (upd G t g) m) :
    P.inv (upd G t (L.set g .wait rnil)) m := by
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi
  have hph : L.pl (upd G t g) t = .spin := by show L.ph (upd G t g t) = _; rw [upd_self]; exact hg
  have hnh : L.pl (upd G t g) t ≠ .holds := by rw [hph]; decide
  have hng : L.pl (upd G t g) t ≠ .gone := by rw [hph]; decide
  have hl := hiL.w.queue (c := m.current) (ws := m.waiters) (wk := m.woken) (p := .wait) hnh hng
    (by decide) (by decide) (fq_keep hiL.w (by rw [hph]; decide) (by rw [hph]; decide))
    (wit_keep hiL.w hnh (by decide) fun _ => rfl)
  have hm : ({ m with current := m.current, waiters := m.waiters, woken := m.woken } : Mem) = m := by
    cases m; rfl
  rw [hm] at hl
  have := hP.stepAt (G₁ := upd G t g) (upd_self _ _ _) hok (by rw [hg]; decide)
    (by rw [hg]; decide) (by decide) hiL hU (Step.same rfl rfl rfl rfl rfl rfl fun _ _ => Iff.rfl) hl
  rwa [upd_upd] at this

/-- `tryLock`, `or(1)` with an acquire, by thread `t` at `out` (`g`). -/
theorem wp_orLock (hP : L.Fits K P U ok) (hc3 : L.c = 3) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = 0 ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       ((r = 1 ∨ r = 3) ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .or false .acquire 4 L.ptr (1 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n := by
  unfold atomicRmwC
  refine hP.pick (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.rmw_noErr
      ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .out := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hcase⟩ := hiL.w.orLock hc3 hph rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rcases hcase with ⟨hr', hF, hw, hacq⟩ | ⟨hr', hw⟩
  · exact .inl ⟨hr', hP.stepAcq hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) hiL hU hst
      hF hacq hw⟩
  · exact .inr ⟨hr', hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide)
      hiL hU hst hw⟩

/-- `tryLock` off x86, a weak acquire `cmpxchg` `0 → 1` (`WInv.casWeakLock`), by thread `t` at
`out` (`g`): it holds the lock, or (any failure, spurious ones too) it is at `spin`. -/
theorem wp_casWeakLock (hP : L.Fits K P U ok) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       ((∃ v, r = some v) ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakC (n := 32) .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1 :
      CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgWeakC
  refine hP.pick (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.casWeakLock_noErr
      ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .out := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hcase⟩ := hiL.w.casWeakLock hph rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rcases hcase with ⟨hr', hF, hw, hacq⟩ | ⟨hr', hw⟩
  · exact .inl ⟨hr', hP.stepAcq hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) hiL hU hst
      hF hacq hw⟩
  · exact .inr ⟨hr', hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide)
      hiL hU hst hw⟩

/-- A relaxed load of the word by thread `t` (`g`, not `gone`): no place changes. -/
theorem wp_loadLock (hP : L.Fits K P U ok) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g ≠ .gone) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t → P.inv (upd G₁ t g) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .relaxed 4 L.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  refine hP.pick hg hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.load_noErr ((hiL.ht (t := t) (by rw [hg₁]; exact hg)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁]; exact hg) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  obtain ⟨hst, hcu, hl⟩ := hiL.w.load rfl ((hiL.ht (t := t) (by rw [hg₁]; exact hg)).1) rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rw [← hg₁, upd_same]
  exact hP.stay hU (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hg) hst (hiL.lstay hst hl)

/-- `os_unfair_lock_lock`'s `cmpxchg` `0 → 1`, by thread `t` at `out` or `spin` (`g`). -/
theorem wp_casD (hP : L.Fits K P U ok) (hc1 : L.c = 1) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out ∨ L.ph g = .spin) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r = some (BitVec.ofNat 32 L.c) ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgC (n := 32) .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1 : CM Tgt σ _).run s)
      Q G m n := by
  have hnh : L.ph g ≠ .holds := by rcases hg with h | h <;> rw [h] <;> decide
  have hng : L.ph g ≠ .gone := by rcases hg with h | h <;> rw [h] <;> decide
  unfold cmpxchgC
  refine hP.pick hng hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.cmpxchgAt_noErr ((hiL.ht (t := t) (by rw [hg₁]; exact hng)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁]; exact hng) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .out ∨ L.pl G₁ t = .spin := by
    show L.ph (G₁ t) = _ ∨ L.ph (G₁ t) = _; rw [hg₁]; exact hg
  obtain ⟨hst, hcu, hcase⟩ := hiL.w.casD hc1 hph rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rcases hcase with ⟨rfl, hF, hw, hacq⟩ | ⟨rfl, hw⟩
  · exact .inl ⟨rfl, hP.stepAcq hg₁ hok hng hnh hiL hU hst hF hacq hw⟩
  · exact .inr ⟨rfl, hP.stepAt hg₁ hok hng hnh (by decide) hiL hU hst hw⟩

/-- `os_unfair_lock_lock`'s futex wait for `1`, by thread `t` at `wait` (`g`). -/
theorem wp_waitD (hP : L.Fits K P U ok) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((threadFutexWaitC L.ptr (BitVec.ofNat 32 L.c) : CM Tgt σ Unit).run s) Q G m n := by
  rw [threadFutexWaitC_eq]
  exact wp_futexWaitOn hP (BitVec.setWidth_eq _) hg hok hi h

/-- `os_unfair_lock_unlock`'s `xchg` of `0` with a release, by the holder `t` (`g`). -/
theorem wp_xchgRel (hP : L.Fits K P U ok) (hc1 : L.c = 1) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      P.inv (upd G₁ t (L.set g .wake rnil)) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .xchg false .release 4 L.ptr (0 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n := by
  unfold atomicRmwC
  refine hP.pick (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.rmw_noErr ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .holds := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hbf, hw, hrel⟩ := hiL.w.xchgRel hc1 hph rfl hr
  exact ⟨hst.threads, h k hk G₁ m' r hcu
    (hP.stepRel hg₁ hok hg (by decide) hiL hU hst hbf hrel hw)⟩

/-! ### The OS futex (`Os.futexWait`, `Os.futexWake`; premises OSF-01, OSF-02)

The word at std's translated `Thread.Futex` (`ZigLean/Sep/Full/OsFutex.lean`). At the OS wait
the thread is at `spin` over the oracle's pick and the kernel's compare, and goes to `wait` only
when it sleeps, in the same turn: at the pick the protocol knows nothing about the futex queue (a
timed waiter is runnable while it is queued, so no global fact says that a resumed thread is not
queued), and `spin` is not a queue place (`LockWord.Queue`), so the scheduler's wait gets its
premise (`WInv.wait`, `WInv.spurious`) from the `wait` stop. -/

/-- The same memory, but the OS state. -/
theorem _root_.Zig.Full.LockWord.WInv.osState {L : LockWord} {Pl : ThreadId → LPh} {m : Mem}
    (hi : L.WInv Pl m) (o : OsState) : L.WInv Pl { m with os := o } :=
  ⟨hi.csize, hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok, hi.loc.plain⟩, hi.wfp,
    hi.rel, hi.fq, hi.wit, hi.owner⟩

/-- A change of the OS state only (an interrupt's delivery, `Os.takeInterrupt`) by a thread in
the lock's code keeps the protocol's invariant. -/
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
    (h : (Os.takeInterrupt.run m).run = some (.ok (b, m'))) : P.inv G m' := by
  obtain ⟨o, rfl⟩ := Os.takeInterrupt_os h
  exact hP.osState hi hok hng o

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
  · exact hP.takeInterrupt hi (by rw [upd_self]; exact hok) (by rw [upd_self]; exact hng) h₀
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
  -- after the wait, at `spin`: the interrupt's delivery keeps the invariant
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

/-- **`unlock`'s OS futex wake** (`Os.futexWake`, OSF-02) of up to `w ≥ 1` waiters (or all) at the
lock's word, by thread `t` at `wake` (`g`): after a wake it goes on at `out`; after a spurious
`EINTR` (macOS; nobody woken) it is still at `wake` (std wakes again). -/
theorem wp_osWake (hP : L.Fits K P U ok) {w : Option Nat} (hw : ∀ k, w = some k → 1 ≤ k)
    {spurious : Bool} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}
    (hg : L.ph g = .wake) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ r G₁ m', m'.current = t →
      ((∃ j, r = some j) ∧ P.inv (upd G₁ t (L.set g .out rnil)) m' ∨
       r = none ∧ P.inv (upd G₁ t g) m') → Q r G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWake L.ptr w spurious : ConcM Tgt (Option Nat)) Q G m n := by
  refine WP.osFutexWake fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ => ⟨fun cs m' hr => ?_, fun _ => ?_⟩⟩
  · obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
    have hph : L.pl G₁ t = .wake := by show L.ph (G₁ t) = _; rw [hg₁, hg]
    obtain ⟨c, hc, hr'⟩ := Os.futexWake_pos (m := { m₁ with current := t }) hw hr
    obtain ⟨hst, hcu, hl⟩ := hiL.w.wake hph hc hr'
    exact h k hk _ G₁ m' hcu (.inl ⟨⟨_, rfl⟩, hP.stepAt hg₁ hok (by rw [hg]; decide)
      (by rw [hg]; decide) (by decide) hiL hU hst hl⟩)
  · have hng : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
    obtain ⟨-, -, -, hic⟩ := hP.cur t hi₁ hng
    exact h k hk none G₁ _ rfl (.inr ⟨rfl, by rw [← hg₁, upd_same]; exact hic⟩)

end FLock

end Full
end Zig
