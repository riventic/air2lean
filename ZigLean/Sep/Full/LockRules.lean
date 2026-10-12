import ZigLean.Sep.Full.Lock

/-!
# The rules of a lock's code, over full-state resources

The steps of `Io.Mutex`'s code (`lock`, `unlock`; translated from Zig 0.16.0's std code) and of
`Thread.Mutex`'s code (0.15.2: `FutexImpl` on Linux, `os_unfair_lock` on macOS) on the word of a
lock `L : FLock γ` (`ZigLean/Sep/Full/Lock.lean`), proved once for every protocol that has the
lock (`FLock.Fits`, `FLock.FitsOn`). Each rule is a stop (the pick of the op, or the futex op) and
then the op; it gives the protocol's invariant with the thread's new place. The word's part of
each op is `ZigLean/Sep/Full/LockWord.lean` (`WInv.cas`, `WInv.xchgLock`, …); the resource moves
with `Inv.acq` (into the acquiring thread's part) and `Inv.rel` (back into the rest).

| Rule | Op | Place before | Place after |
|---|---|---|---|
| `wp_cas` | `cmpxchg(0 → 1)`, acquire | `out` | `holds` (with the resource), `spin` (read `1`), `wait` (read `c`) |
| `wp_orLock` | `or(1)`, acquire (`c = 3`) | `out` | `holds` (read `0`), or `spin` (read `1` or `3`) |
| `wp_loadLock` | load, relaxed | any but `gone` | the same |
| `Fits.toWait` | (no op) | `spin` | `wait` |
| `wp_xchgLock` | `xchg(c)`, acquire | `spin` | `holds` (read `0`), or `wait` |
| `wp_wait`, `wp_waitD` | futex wait for `c` | `wait` | `spin` |
| `wp_xchgUnlock` | `xchg(0)`, release | `holds` | `out` (read `1`), or `wake` (read `c`); the lock gets the resource |
| `wp_xchgRel` | `xchg(0)`, release (`c = 1`) | `holds` | `wake` |
| `wp_casD` | `cmpxchg(0 → 1)`, acquire (`c = 1`) | `out` or `spin` | `holds`, or `wait` |
| `wp_wake` | futex wake of 1 | `wake` | `out` |
-/

namespace Zig
namespace Full

open FAssn Conc Proto LockWord

namespace FLock

variable {γ : Type} {L : FLock γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## A protocol with the lock -/

/-- If every thread has ended, sleeps at a futex or waits at a join, no thread waits at the
word. -/
theorem FitsOn.noWaits (hP : L.FitsOn P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem}
    (hi : L.Inv G rX m)
    (hall : ∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) :
    ¬ L.Waits m.waiters := fun hp => by
  obtain ⟨v, hv, hq, hb, -⟩ := hi.w.wit hp
  rcases hall v hv with h | h | h
  · have := hP.fin _ h; simp only [pl] at hb; rw [this] at hb; cases hb
  · rw [hq] at h; cases h
  · have := hP.joins _ h; simp only [pl] at hb; rw [this] at hb; cases hb

/-- A thread at `lock`'s futex wait is not the last one (`FitsOn.noWaits`). -/
theorem FitsOn.live (hP : L.FitsOn P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem}
    (hi : L.Inv G rX m) {t : ThreadId} (ht : L.ph (G t) = .wait) : P.Live t G m := by
  intro hw hall
  apply hP.noWaits hi hall
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hw
  have he : (m.waiters[i]).1 = t := by simpa using he
  rcases hi.w.fq _ (Array.getElem_mem hi') with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Array.any_eq_true.mpr ⟨i, hi', by simp [h1]⟩
  · simp only [pl] at h2; rw [he, ht] at h2; cases h2

/-- A lock step with `t`'s new place and resource keeps the protocol's invariant. -/
theorem FitsOn.step (hP : L.FitsOn P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {p : LPh} {h : Res} (hU : U G rX m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone)
    (hs : L.Step t m m') (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!))
    (hl : L.Inv (upd G t (L.set (G t) p h)) rX m') : P.inv (upd G t (L.set (G t) p h)) m' :=
  (hP.inv _ _).mpr ⟨rX, hl, hP.stable G rX m m' t p h hok hph hU hs hrel⟩

/-- A lock step with the same ghost values keeps the protocol's invariant. -/
theorem FitsOn.stay (hP : L.FitsOn P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
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
theorem FitsOn.cur (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem} (t : ThreadId)
    (hi : P.inv G m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone) :
    ∃ rX, L.Inv G rX { m with current := t } ∧ U G rX m ∧ P.inv G { m with current := t } := by
  obtain ⟨rX, hiL, hU⟩ := (hP.inv G m).mp hi
  exact ⟨rX, hiL.cur t, hU, hP.stay hU hok hph (Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl))
    (hiL.cur t)⟩

/-- `U` at a stop of `t`. -/
theorem FitsOn.curU (hP : L.FitsOn P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem} (t : ThreadId)
    (hU : U G rX m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone) : U G rX { m with current := t } := by
  have := hP.stable G rX m { m with current := t } t (L.ph (G t)) (L.held (G t)) hok hph hU
    (Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)) (fun h1 h2 => absurd h1 h2)
  rwa [upd_set_self] at this

/-! ## The ops in generated code (`WP`) -/

variable {σ α : Type} [Packed α 32]

/-- The common shape of an op's rule: a pick, then a `MemM` op of `t` from the invariant at the
stop. -/
theorem FitsOn.pick {count : Mem → Nat} {x : Nat → MemM β} (hP : L.FitsOn P U ok) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hok : ok g)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : β × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hnoErr : ∀ (G₁ : ThreadId → γ) (rX : Res) (m₁ : Mem) (c : Nat), G₁ t = g → L.Inv G₁ rX { m₁ with current := t } →
      (c < count { m₁ with current := t } ∨ count { m₁ with current := t } = 0 ∧ c = 0) →
      ∀ e, ((x c).run { m₁ with current := t }).run ≠ some (.error e))
    (h : ∀ k, n = k + 1 → ∀ (G₁ : ThreadId → γ) (rX : Res) (m₁ : Mem) (c : Nat) (r : β) (m' : Mem), G₁ t = g → L.Inv G₁ rX { m₁ with current := t } →
      U G₁ rX { m₁ with current := t } →
      ((x c).run { m₁ with current := t }).run = some (.ok (r, m')) → m'.threads = m₁.threads ∧
      Q (r, s) G₁ m' k) :
    P.WP t ((do let c ← (pickC count : CM Tgt σ Nat); callMC (x c)).run s) Q G m n := by
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hgone₁ : L.ph (G₁ t) ≠ .gone := by rw [hg₁]; exact hgone
  obtain ⟨rX, hiL, hU, -⟩ := hP.cur t hi₁ hok₁ hgone₁
  have hU' := hP.curU t hU hok₁ hgone₁
  refine WP.callMC (fun e he => (hnoErr G₁ rX m₁ c hg₁ hiL hcr e he).elim) fun r m' hr => ?_
  obtain ⟨h1, h2⟩ := h k hk G₁ rX m₁ c r m' hg₁ hiL hU' hr
  exact ⟨by rw [h1], h2⟩

/-- `lock`'s first try, `cmpxchg(unlocked → locked_once)`, by thread `t` at `out` (`g`). -/
theorem wp_casOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r = some S.one ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m') ∨
       (r = some S.two ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((cmpxchgAsC .acquire .relaxed 4 L.ptr S.unl S.one : CM Tgt σ (Option α)).run s)
      Q G m n := by
  unfold cmpxchgAsC
  refine hP.pick hok (by rw [hg]; decide) hi
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
theorem FitsOn.stepAt (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ} {rX : Res} {m₁ m' : Mem}
    {t : ThreadId} {g : γ} {p : LPh} (hg₁ : G₁ t = g) (hok : ok g) (hng : L.ph g ≠ .gone)
    (hnh : L.ph g ≠ .holds) (hp : p ≠ .holds) (hiL : L.Inv G₁ rX m₁) (hU : U G₁ rX m₁)
    (hst : L.Step t m₁ m') (hw : L.WInv (upd (L.pl G₁) t p) m') :
    P.inv (upd G₁ t (L.set g p rnil)) m' := by
  subst hg₁
  exact hP.step hU hok hng hst (fun h => absurd h hnh) (hiL.lstepAt hst hnh hng hp hw)

/-- An acquire of `t` as the protocol's invariant. -/
theorem FitsOn.stepAcq (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ} {rX : Res} {m₁ m' : Mem}
    {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hok : ok g) (hng : L.ph g ≠ .gone)
    (hnh : L.ph g ≠ .holds) (hiL : L.Inv G₁ rX m₁) (hU : U G₁ rX m₁)
    (hst : L.Step t m₁ m') (hF : L.Free G₁) (hacq : L.Acq (L.pl G₁) t m₁ m')
    (hw : L.WInv (upd (L.pl G₁) t .holds) m') :
    ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m' := by
  subst hg₁
  obtain ⟨rL, -, hl⟩ := hiL.acq hst hnh hng hF hacq hw
  exact ⟨rL, hP.step hU hok hng hst (fun h => absurd h hnh) hl⟩

/-- A release of the holder `t` as the protocol's invariant. -/
theorem FitsOn.stepRel (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ} {rX : Res} {m₁ m' : Mem}
    {t : ThreadId} {g : γ} {p : LPh} (hg₁ : G₁ t = g) (hok : ok g) (hph : L.ph g = .holds)
    (hp : p ≠ .holds) (hiL : L.Inv G₁ rX m₁) (hU : U G₁ rX m₁) (hst : L.Step t m₁ m')
    (hbf : L.Before m' (m₁.clocks[t]!)) (hrel : L.Rel t (upd (L.pl G₁) t p) m₁ m')
    (hw : L.WInv (upd (L.pl G₁) t p) m') :
    P.inv (upd G₁ t (L.set g p rnil)) m' := by
  subst hg₁
  exact hP.step hU hok (by rw [hph]; decide) hst (fun _ _ => hbf) (hiL.rel hst hph hp hrel hw)

/-- `lock`'s loop, `xchg(contended)`, by thread `t` at `spin` (`g`). -/
theorem wp_xchgLockOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .spin)
    (hok : ok g) (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.unl ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r ≠ S.unl ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .acquire 4 L.ptr S.two : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  refine hP.pick hok (by rw [hg]; decide) hi
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
theorem wp_xchgUnlockOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds)
    (hok : ok g) (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.one ∧ P.inv (upd G₁ t (L.set g .out rnil)) m') ∨
       (r = S.two ∧ P.inv (upd G₁ t (L.set g .wake rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .release 4 L.ptr S.unl : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  refine hP.pick hok (by rw [hg]; decide) hi
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
theorem wp_futexWaitOn (hP : L.FitsOn P U ok) {ε : Type} {w : Nat} [Packed ε w] {io : Io}
    {e : ε} (he : (Packed.toBits e).setWidth 32 = BitVec.ofNat 32 L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWaitC io L.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWaitC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  simp only [he]
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  have hph : L.pl G₁ t = .wait := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hng : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  refine ⟨fun _ => hP.live hiL (by rw [hg₁]; exact hg), fun hq => ⟨fun _ =>
    hiL.w.wait_ok (hiL.ht hng).1 hng, fun b m' hw => ?_⟩⟩
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
theorem wp_waitOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {io : Io} {s : σ}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait)
    (hok : ok g) (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWaitC io L.ptr S.two : CM Tgt σ Unit).run s) Q G m n :=
  wp_futexWaitOn hP (by rw [S.bits2, hS]; rfl) hg hok hi h

/-- `unlock`'s futex wake of one waiter, by thread `t` at `wake` (`g`): it goes on at `out`. -/
theorem wp_wakeOn (hP : L.FitsOn P U ok) {io : Io} {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wake) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .out rnil)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWakeC io L.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWakeC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ cs m' hw => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  have hph : L.pl G₁ t = .wake := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hl⟩ := hiL.w.wake hph (by decide) hw
  exact h k hk G₁ m' hcu
    (hP.stepAt hg₁ hok (by rw [hg]; decide) (by rw [hg]; decide) (by decide) hiL hU hst hl)

/-! ### `Fits`: every thread runs the lock's code -/

theorem wp_cas (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r = some S.one ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m') ∨
       (r = some S.two ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((cmpxchgAsC .acquire .relaxed 4 L.ptr S.unl S.one : CM Tgt σ (Option α)).run s)
      Q G m n := wp_casOn hP.on S hS hg trivial hi h

theorem wp_xchgLock (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .spin) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.unl ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r ≠ S.unl ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .acquire 4 L.ptr S.two : CM Tgt σ α).run s) Q G m n :=
  wp_xchgLockOn hP.on S hS hg trivial hi h

theorem wp_xchgUnlock (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.one ∧ P.inv (upd G₁ t (L.set g .out rnil)) m') ∨
       (r = S.two ∧ P.inv (upd G₁ t (L.set g .wake rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .release 4 L.ptr S.unl : CM Tgt σ α).run s) Q G m n :=
  wp_xchgUnlockOn hP.on S hS hg trivial hi h

theorem wp_wait (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {io : Io} {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWaitC io L.ptr S.two : CM Tgt σ Unit).run s) Q G m n :=
  wp_waitOn hP.on S hS hg trivial hi h

theorem wp_wake (hP : L.Fits P U) {io : Io} {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wake) (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .out rnil)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWakeC io L.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n :=
  wp_wakeOn hP.on hg trivial hi h

/-! ### `Thread.Mutex` (0.15.2): the ops on bits

Stated for `FitsOn` (a thread with `ok` runs the lock's code), as `MutexImpl` quantifies over it;
`Fits` gives them through `Fits.on` with `trivial`. -/

/-- A thread at `spin` (`g`) goes to the futex wait: no memory step. -/
theorem FitsOn.toWait (hP : L.FitsOn P U ok) {t : ThreadId} {G : ThreadId → γ} {m : Mem} {g : γ}
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
theorem wp_orLock (hP : L.FitsOn P U ok) (hc3 : L.c = 3) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = 0 ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       ((r = 1 ∨ r = 3) ∧ P.inv (upd G₁ t (L.set g .spin rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwC .or false .acquire 4 L.ptr (1 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n := by
  unfold atomicRmwC
  refine hP.pick hok (by rw [hg]; decide) hi
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

/-- A relaxed load of the word by thread `t` (`g`, not `gone`): no place changes. -/
theorem wp_loadLock (hP : L.FitsOn P U ok) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g ≠ .gone) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t → P.inv (upd G₁ t g) m' → Q (r, s) G₁ m' k) :
    P.WP t ((atomicLoadC (n := 32) .relaxed 4 L.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  refine hP.pick hok hg hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.load_noErr ((hiL.ht (t := t) (by rw [hg₁]; exact hg)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁]; exact hg) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  obtain ⟨hst, hcu, hl⟩ := hiL.w.load rfl ((hiL.ht (t := t) (by rw [hg₁]; exact hg)).1) rfl hr
  refine ⟨hst.threads, h k hk G₁ m' r hcu ?_⟩
  rw [← hg₁, upd_same]
  exact hP.stay hU (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hg) hst (hiL.lstay hst hl)

/-- `os_unfair_lock_lock`'s `cmpxchg` `0 → 1`, by thread `t` at `out` or `spin` (`g`). -/
theorem wp_casD (hP : L.FitsOn P U ok) (hc1 : L.c = 1) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out ∨ L.ph g = .spin) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ rL, P.inv (upd G₁ t (L.set g .holds rL)) m') ∨
       (r = some (BitVec.ofNat 32 L.c) ∧ P.inv (upd G₁ t (L.set g .wait rnil)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((cmpxchgC (n := 32) .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1 : CM Tgt σ _).run s)
      Q G m n := by
  have hnh : L.ph g ≠ .holds := by rcases hg with h | h <;> rw [h] <;> decide
  have hng : L.ph g ≠ .gone := by rcases hg with h | h <;> rw [h] <;> decide
  unfold cmpxchgC
  refine hP.pick hok hng hi
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
theorem wp_waitD (hP : L.FitsOn P U ok) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin rnil)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((threadFutexWaitC L.ptr (BitVec.ofNat 32 L.c) : CM Tgt σ Unit).run s) Q G m n := by
  rw [threadFutexWaitC_eq]
  exact wp_futexWaitOn hP (BitVec.setWidth_eq _) hg hok hi h

/-- `os_unfair_lock_unlock`'s `xchg` of `0` with a release, by the holder `t` (`g`). -/
theorem wp_xchgRel (hP : L.FitsOn P U ok) (hc1 : L.c = 1) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      P.inv (upd G₁ t (L.set g .wake rnil)) m' → Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwC .xchg false .release 4 L.ptr (0 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n := by
  unfold atomicRmwC
  refine hP.pick hok (by rw [hg]; decide) hi
    (fun G₁ rX m₁ c hg₁ hiL hcr => hiL.w.rmw_noErr ((hiL.ht (t := t) (by rw [hg₁, hg]; decide)).1)
      (by show L.ph (G₁ t) ≠ _; rw [hg₁, hg]; decide) hcr)
    fun k hk G₁ rX m₁ c r m' hg₁ hiL hU hr => ?_
  have hph : L.pl G₁ t = .holds := by show L.ph (G₁ t) = _; rw [hg₁, hg]
  obtain ⟨hst, hcu, hbf, hw, hrel⟩ := hiL.w.xchgRel hc1 hph rfl hr
  exact ⟨hst.threads, h k hk G₁ m' r hcu
    (hP.stepRel hg₁ hok hg (by decide) hiL hU hst hbf hrel hw)⟩

end FLock

end Full
end Zig
