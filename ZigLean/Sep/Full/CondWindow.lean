import ZigLean.Sep.Full.Sem

/-!
# The epoch window of a condition with one registered waiter at a time

`FCond.Fits.win` (`ZigLean/Sep/Full/Cond.lean`) asks the client's rest to bound the epoch writes
after a registered waiter's saved one below `2^32` (`FCond.Win`). With at most one registered
waiter at a time and every epoch write before the mutex's holder (`FLock.WordHB`, so the waiter's
load saves the newest write: `FCond.ld_newest`), the client bounds the window by the posts per
registration: while a waiter is registered, at most one post and so at most one epoch write
happens. This module states those facts once for every condition and lock (`FCond.Win1`) and
keeps them over every step of the condition's code (`Win1.step`) and of a semaphore's
(`Win1.semStep`), so a client keeps `Win1` in its rest and gets `FCond.Win` (`Win1.win`). The
client gives only what its own protocol decides: that a thread in the signal code holds the
mutex (`Win1.step`'s `hsh`; for a semaphore its invariant gives it), and that no waiter is
registered when one enters the wait (`Win1.semStep`'s `hent`).

The facts (`Win1`):
- `one`: at most one registered waiter;
- `ehb`: every epoch write happened before the mutex's holder;
- `f0`: a waiter at its load saved the newest epoch write;
- `rc`: no thread is in the critical code (`en`, `ld`) while one is registered, so `one` stays: a
  registration comes from the load;
- `f2`, `f3`, `f4`, `incS`: while a waiter is registered at most one epoch write follows its saved
  one (`f2`), none yet while a signaller is between its post and its epoch write (`f3`), and after
  it every registered waiter is signalled (`f4`), as after every post (`incS`), so no post follows.

This is the single-waiter case of ledger rows `cond-epoch-load-floor` and
`cond-window-multi-waiter`; two or more registered waiters stay open there.
-/

namespace Zig
namespace Full

open Conc Proto

namespace FCond

variable {γ : Type} {C : FCond γ} {L : FLock γ}

variable (C L) in
/-- **The window of a condition with one registered waiter at a time** (module doc). -/
structure Win1 (G : ThreadId → γ) (m : Mem) : Prop where
  /-- At most one registered waiter. -/
  one : ∀ u v, (C.ph (G u)).isReg = true → (C.ph (G v)).isReg = true → u = v
  /-- Every epoch write happened before the mutex's holder (`ld_newest`). -/
  ehb : L.WordHB C.Ep G m
  /-- A waiter at its load saved the newest epoch write. -/
  f0 : ∀ u i e, C.ph (G u) = .ld i e → (C.Ep.hist m).size = i + 1
  /-- No thread is in the condition's critical code while one is registered. -/
  rc : ∀ u v, (C.ph (G u)).isReg = true → (C.ph (G v)).crit = true → False
  /-- While a waiter is registered, at most one epoch write happens after its saved one … -/
  f2 : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → (C.Ep.hist m).size ≤ i + 2
  /-- … none yet while a signaller is between its post and its epoch write … -/
  f3 : ∀ u i jr sn e v q n h, C.ph (G u) = .reg i jr sn e → C.ph (G v) = .inc q n h →
    (C.Ep.hist m).size ≤ i + 1
  /-- … and after it every registered waiter is signalled, so no post follows. -/
  f4 : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → (C.Ep.hist m).size = i + 2 → C.Sated m
  /-- After a post, every registered waiter is signalled. -/
  incS : ∀ v q n h, C.ph (G v) = .inc q n h → C.Sated m

/-- **The window from `Win1`**: a registered waiter has at most two epoch writes after its saved
one (`f2`). -/
theorem Win1.win {U : (ThreadId → γ) → Res → Mem → Prop}
    (h : ∀ G rX m, U G rX m → C.Win1 L G m) : C.Win U :=
  fun G rX m hu u i jr e hc _ _ => by
    have := (h G rX m hu).f2 u i jr false e hc
    omega

/-- `Win1` with no thread in the condition's code. -/
theorem Win1.of_out {G : ThreadId → γ} {m : Mem} (hout : ∀ u, C.ph (G u) = .out)
    (ehb : L.WordHB C.Ep G m) : C.Win1 L G m := by
  refine ⟨fun u _ hu => ?_, ehb, fun u _ _ h => ?_, fun u _ hu => ?_, fun u _ _ _ _ h => ?_,
    fun u _ _ _ _ _ _ _ _ h => ?_, fun u _ _ _ _ h => ?_, fun u _ _ _ h => ?_⟩ <;>
    first
    | (rw [hout u] at hu; cases hu)
    | (rw [hout u] at h; cases h)

/-- **`Win1` over a step that keeps every thread's place in the condition's code and the
condition's writes**, with `ehb` after it given. -/
theorem Win1.keep {G G' : ThreadId → γ} {m m' : Mem} (hw : C.Win1 L G m)
    (hc : ∀ u, C.ph (G' u) = C.ph (G u)) (hS : C.S.hist m' = C.S.hist m)
    (hE : C.Ep.hist m' = C.Ep.hist m) (ehb : L.WordHB C.Ep G' m') : C.Win1 L G' m' := by
  have hsat : C.Sated m' ↔ C.Sated m := Sated.congr hS
  exact ⟨fun u v hu hv => by rw [hc] at hu hv; exact hw.one u v hu hv, ehb,
    fun u i e h => by rw [hc u] at h; rw [hE]; exact hw.f0 u i e h,
    fun u v hr hc' => by rw [hc u] at hr; rw [hc v] at hc'; exact hw.rc u v hr hc',
    fun u i jr sn e h => by rw [hc u] at h; rw [hE]; exact hw.f2 u i jr sn e h,
    fun u i jr sn e v q n h hu hv => by
      rw [hc u] at hu; rw [hc v] at hv; rw [hE]; exact hw.f3 u i jr sn e v q n h hu hv,
    fun u i jr sn e h hs => by
      rw [hc u] at h; rw [hE] at hs; exact hsat.mpr (hw.f4 u i jr sn e h hs),
    fun v q n h hv => by rw [hc v] at hv; exact hsat.mpr (hw.incS v q n h hv)⟩

/-- **`Win1` over a waiter's entry `out → en`** (a semaphore's `Move.enter`) while no waiter is
registered, with `ehb` after it given. -/
theorem Win1.enter {G G' : ThreadId → γ} {m : Mem} {t : ThreadId} (hw : C.Win1 L G m)
    (ht : C.ph (G' t) = .en) (hG : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u))
    (hnr : ∀ u, (C.ph (G u)).isReg = false) (ehb : L.WordHB C.Ep G' m) : C.Win1 L G' m := by
  -- a thread at another place than `en` is not `t`
  have hne : ∀ u, C.ph (G' u) ≠ .en → C.ph (G' u) = C.ph (G u) := fun u h => by
    by_cases e : u = t
    · subst e; exact absurd ht h
    · exact hG u e
  have hreg : ∀ u, (C.ph (G' u)).isReg = true → False := fun u h => by
    have h' := h
    rw [hne u fun e => by rw [e] at h; cases h, hnr u] at h'
    cases h'
  exact ⟨fun u _ hu => (hreg u hu).elim, ehb,
    fun u i e h => by rw [hne u (by rw [h]; nofun)] at h; exact hw.f0 u i e h,
    fun u _ hr _ => hreg u hr,
    fun u i jr sn e h => by rw [hne u (by rw [h]; nofun)] at h; exact hw.f2 u i jr sn e h,
    fun u i jr sn e v q n h hu hv => by
      rw [hne u (by rw [hu]; nofun)] at hu; rw [hne v (by rw [hv]; nofun)] at hv
      exact hw.f3 u i jr sn e v q n h hu hv,
    fun u i jr sn e h hs => by
      rw [hne u (by rw [h]; nofun)] at h; exact hw.f4 u i jr sn e h hs,
    fun v q n h hv => by rw [hne v (by rw [hv]; nofun)] at hv; exact hw.incS v q n h hv⟩

/-! ## The state's writes -/

/-- The newest `waiters` does not rise when no thread becomes registered (`Inv.cnt`). -/
theorem wOf_le {G G' : ThreadId → γ} {m m' : Mem} (hI : C.Inv L G m) (hI' : C.Inv L G' m')
    (h : ∀ u, (C.ph (G' u)).isReg = true → (C.ph (G u)).isReg = true) :
    wOf (C.lastS m') ≤ wOf (C.lastS m) := by
  obtain ⟨T, hT, hw, -⟩ := hI.cnt
  obtain ⟨T', hT', hw', -⟩ := hI'.cnt
  rw [hw, hw', ← nreg_ext hT (Nat.le_max_left T T'), ← nreg_ext hT' (Nat.le_max_right T T')]
  exact tsum_le fun u _ => by
    show (if (C.ph (G' u)).isReg then 1 else 0) ≤ (if (C.ph (G u)).isReg then 1 else 0)
    cases h1 : (C.ph (G' u)).isReg
    · simp
    · simp [h u h1]

/-- At most one waiter while at most one thread is registered. -/
theorem wOf_le_one {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m)
    (hone : ∀ u v, (C.ph (G u)).isReg = true → (C.ph (G v)).isReg = true → u = v) :
    wOf (C.lastS m) ≤ 1 := by
  obtain ⟨T, hT, hw, -⟩ := hI.cnt
  -- every registered thread is `v`
  obtain ⟨v, hv⟩ : ∃ v, ∀ u, (C.ph (G u)).isReg = true → u = v := by
    by_cases h : ∃ v, (C.ph (G v)).isReg = true
    · obtain ⟨v, hv⟩ := h; exact ⟨v, fun u hu => hone u v hu hv⟩
    · exact ⟨0, fun u hu => absurd ⟨u, hu⟩ h⟩
  rw [hw, ← nreg_ext hT (Nat.le_max_left T (v + 1))]
  calc C.nreg G (Max.max T (v + 1))
      ≤ tsum (Max.max T (v + 1)) (fun u => if u = v then 1 else 0) := tsum_le fun u _ => by
        show (if (C.ph (G u)).isReg then 1 else 0) ≤ _
        cases h1 : (C.ph (G u)).isReg
        · simp
        · simp [hv u h1]
    _ = 1 := tsum_point (by omega) 1

/-- **`signals = waiters` stays** over a step with the invariant after it in which no thread
becomes registered: the state's writes are kept or get one that registers no thread. -/
theorem Sated.keep {G G' : ThreadId → γ} {m m' : Mem} (hI : C.Inv L G m) (hI' : C.Inv L G' m')
    (hnr : ∀ u, (C.ph (G' u)).isReg = true → (C.ph (G u)).isReg = true)
    (hS : C.S.hist m' = C.S.hist m ∨ ∃ x, C.S.hist m' = (C.S.hist m).push x)
    (hs : C.Sated m) : C.Sated m' := by
  rcases hS with e | ⟨x, e⟩
  · exact (Sated.congr e).mpr hs
  · refine hI'.sated_push hI.spos e hs ?_
    rw [← lastS_push e]; exact wOf_le hI hI' hnr

/-- **A post** (`sl → inc` of `t`): the state's new write raises `signals` (`SigStep.inc_fresh`)
and registers no thread, so it does not follow a sated write, and with at most one waiter it is
sated. -/
theorem post_facts {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId}
    {sh : Array Word.Entry} {c : VClock} {q n : Nat} {h : Array Word.Entry}
    (hI : C.Inv L G m) (hI' : C.Inv L G' m') (hG : ∀ u, u ≠ t → G' u = G u)
    (ht : C.ph (G t) = .sl sh c) (ht' : C.ph (G' t) = .inc q n h)
    (hsg : C.SigStep t (C.ph (G t)) (C.ph (G' t)) m m') :
    ¬ C.Sated m ∧ (wOf (C.lastS m') ≤ 1 → C.Sated m') ∧
      ∃ x, C.S.hist m' = (C.S.hist m).push x := by
  obtain ⟨hq, ⟨x, hx⟩, -, hq0, hlt⟩ := SigStep.inc_fresh ht ht' hG hsg hI hI'
  have hlast' : C.lastS m' = (C.S.hist m')[q]! := by
    rw [lastS_push hx, hx, hq]; exact Word.get_push_eq.symm
  have hlast : C.lastS m = (C.S.hist m')[q - 1]! := by
    have := hI.spos; unfold lastS; rw [hx, hq]; exact (Word.get_push_lt (by omega)).symm
  have hnr : ∀ u, (C.ph (G' u)).isReg = true → (C.ph (G u)).isReg = true := fun u hr => by
    by_cases e : u = t
    · subst e; rw [ht'] at hr; cases hr
    · rwa [hG u e] at hr
  have hw := wOf_le hI hI' hnr
  have hsv := (hI'.sv q (by rw [hx, hq, Array.size_push]; omega)).2
  rw [← hlast'] at hsv
  rw [← hlast', ← hlast] at hlt
  refine ⟨fun hs => ?_, fun h1 => ?_, x, hx⟩
  · unfold Sated at hs; omega
  · unfold Sated; omega

/-! ## A step of the condition's code -/

/-- A place is not both in the critical and in the signal code. -/
theorem crit_sig {p : CPh} (h1 : p.crit = true) (h2 : p.sig = true) : False := by
  cases p <;> simp_all [CPh.crit, CPh.sig]

/-- The condition's cells beside an own-part step's word stay (up to `Cell.norm`): they are in the
rest, which the lock's invariant before and after the step reads (`FLock.Inv.restCell`). -/
theorem cells_own {G G' : ThreadId → γ} {rY : Res} {m m' : Mem} {W : Word 32 4}
    (hsub : (C.prim L).Sub G (rsum (W.cellsR m) rY) m) (hL : L.Inv G (rsum (W.cellsR m) rY) m)
    (hL' : L.Inv G' (rsum (W.cellsR m') rY) m')
    (hcW : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    ∀ V, (V = C.S ∨ V = C.Ep) → ∀ l, V.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
  intro V hV l hl
  by_cases hlW : W.In l
  · exact hcW l hlW
  have hrl : (rsum (W.cellsR m') rY).heap l = (rsum (W.cellsR m) rY).heap l := by
    show ((W.cellsR m').heap ∪ rY.heap) l = ((W.cellsR m).heap ∪ rY.heap) l
    rw [FHeap.union_apply, FHeap.union_apply, cellsAt_none hlW, cellsAt_none hlW]
  obtain ⟨hv, rV, hrV, -⟩ := hsub.2 V hV
  cases e : (rsum (W.cellsR m) rY).heap l with
  | none =>
    refine absurd ?_ (cellsAt_some hl (hv.cellIn hl))
    have e' := e
    rw [hrV] at e'
    show (V.cellsR m).heap l = none
    exact (Option.or_eq_none_iff.mp (by rw [← FHeap.union_apply]; exact e')).1
  | some fc => rw [hL'.restCell (hrl.trans e), hL.restCell e]

/-- **`Win1` over a step of the condition's code** (`FLock.Fits.kstep` of `FCond.prim`; module
doc): at a word (the code's transition, the epoch's writes only at `inc → wk`, the load's and the
post's writes as the code takes them: `SigStep`) or on the stepping thread's own part (the same
places and writes). `hsh`: a thread in the signal code holds the mutex (the client's; a
semaphore's invariant gives it, `Win1.semStep`). `hphl`, `hphp`: the lock's place and part leave
the condition's place; `hap`: the condition's words are apart from the lock's. -/
theorem Win1.step {G G' : ThreadId → γ} {rX rX' : Res} {m m' : Mem} {t : ThreadId}
    (hw : C.Win1 L G m) (hsub : (C.prim L).Sub G rX m)
    (hsh : ∀ u, (C.ph (G u)).sig = true → L.ph (G u) = .holds)
    (hphl : ∀ g q h, C.ph (L.set g q h) = C.ph g) (hphp : ∀ g r, C.ph (L.setPart g r) = C.ph g)
    (hap : ∀ W, (W = C.S ∨ W = C.Ep) → W.ApartL L.toLockWord)
    (hst : (C.prim L).Step t G rX m G' rX' m') : C.Win1 L G' m' := by
  have hI := hsub.1
  obtain ⟨W, rY, hW, rfl, rfl, hY, hI', ⟨p, q, h, ⟨hn, hq, hs, hEp, hsg⟩, hWI, rfl⟩ |
    ⟨r, -, hL, -, hfs, hcW, -, hh, hL', rfl⟩⟩ := id hst
  case inr =>
    -- the own part: the same places, the same writes
    have hfs' := hfs.cells
    have hcells := cells_own hsub hL hL' hcW
    have hsame : ∀ u, upd G t (L.setPart (G t) r) u = G u ∨
        (u = t ∧ upd G t (L.setPart (G t) r) u = L.setPart (G t) r) := fun u => by
      by_cases e : u = t
      · subst e; exact .inr ⟨rfl, upd_self⟩
      · exact .inl (upd_ne _ _ e)
    have hlp : ∀ u, L.ph (upd G t (L.setPart (G t) r) u) = L.ph (G u) := fun u => by
      rcases hsame u with e | ⟨rfl, e⟩ <;> rw [e]; rw [L.ph_setPart]
    refine hw.keep (fun u => by rcases hsame u with e | ⟨rfl, e⟩ <;> rw [e]; rw [hphp])
      (hist_hold hsub hfs' hcells (.inl rfl)) (hist_hold hsub hfs' hcells (.inr rfl))
      (hw.ehb.step (fun _ hc => hc.mono (fun u hu => .inl (by rw [hlp]; exact hu)) hfs'.clock
        (hL.before_fstep hfs') hfs'.threads fun u hg => by rwa [hlp] at hg)
        (.inl (hist_hold hsub hfs' hcells (.inr rfl))))
  -- a step at the word `W`
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t (L.set (C.set (G t) p) q h) := ⟨_, rfl⟩
  rw [← hG'] at hI' hst ⊢
  have hG : ∀ u, u ≠ t → G' u = G u := fun u hu => by rw [hG']; exact upd_ne _ _ hu
  have hct : C.ph (G' t) = p := by rw [hG', upd_self, hphl, C.ph_set]
  have hcu : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u e => by rw [hG u e]
  have hLt : L.ph (G' t) = q := by rw [hG', upd_self, L.ph_set]
  -- the lock places: only a waiter's changes, between `out` and `away`
  have hheld : ∀ u, (L.ph (G u)).held = true → (L.ph (G' u)).held = true := fun u hu => by
    by_cases e : u = t
    · subst e; rw [hLt]
      rcases hq with ⟨rfl, -⟩ | ⟨ho, -, -⟩
      · exact hu
      · rcases ho with ho | ⟨ho, -⟩ <;> rw [ho] at hu <;> cases hu
    · rw [hG u e]; exact hu
  have hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone := fun u hu => by
    by_cases e : u = t
    · subst e; rw [hLt] at hu
      rcases hq with ⟨rfl, -⟩ | ⟨ho, -, -⟩
      · exact hu
      · rcases ho with ho | ⟨ho, -⟩ <;> rw [ho] <;> decide
    · rwa [hG u e] at hu
  have hbef : ∀ c, L.Before m c → L.Before m' c := fun _ ⟨i, l, hl, hc⟩ =>
    ⟨i, l, hs.lockLoc (hap W hW) (hap C.Ep (.inr rfl)) hl, hc⟩
  have hhb : ∀ c, L.HB G m c → L.HB G' m' c := fun _ hc =>
    hc.mono (fun u hu => .inl (hheld u hu)) hs.clocks hbef hs.threads hgone
  -- the state's and the epoch's writes
  have hSh : C.S.hist m' = C.S.hist m ∨ ∃ x, C.S.hist m' = (C.S.hist m).push x := by
    rcases (hs.word_rmw (hsub.2 C.S (.inl rfl)).1 (words_apart (.inl rfl) hW)
      (words_apart (.inl rfl) (.inr rfl))).2 with e | ⟨-, -, -, e⟩
    · exact .inl e
    · exact .inr ⟨_, e⟩
  have hEh := (hs.word_rmw (hsub.2 C.Ep (.inr rfl)).1 (words_apart (.inr rfl) hW)
    (words_apart (.inr rfl) (.inr rfl))).2
  -- the epoch's writes: kept, or `t`'s `epoch += 1` at `inc → wk`
  have hEw : C.Ep.hist m' = C.Ep.hist m ∨ ((∃ q n h', C.ph (G t) = .inc q n h') ∧
      (C.Ep.hist m').size = (C.Ep.hist m).size + 1 ∧ ∃ x : Word.Entry, x.clock = m'.clocks[t]! ∧
        C.Ep.hist m' = (C.Ep.hist m).push x) := by
    rcases hEp with e | ⟨q₀, n₀, h₀, e, -⟩
    · exact .inl e
    · rcases hEh with e' | ⟨-, ord, v, e'⟩
      · exact .inl e'
      · exact .inr ⟨⟨q₀, n₀, h₀, e⟩, by rw [e', Array.size_push], _, rfl, e'⟩
  have hincE : ∀ q n h', C.ph (G t) = .inc q n h' → (C.ph (G t)).sig = true := fun _ _ _ e => by
    rw [e]; rfl
  -- two threads in the signal code are one (both hold the mutex)
  have hsig1 : ∀ u v, (C.ph (G u)).sig = true → (C.ph (G v)).sig = true → u = v := fun u v h1 h2 =>
    hWI.one u v (LPh.held_of_holds (hsh u h1)) (LPh.held_of_holds (hsh v h2))
  -- no thread in the critical code while one is in the signal code (both hold the mutex)
  have hcp : ∀ u v, (C.ph (G u)).crit = true → (C.ph (G v)).sig = true → False := fun u v h1 h2 => by
    have e := hWI.one u v (LPh.held_of_holds (hI.crit u h1)) (LPh.held_of_holds (hsh v h2))
    subst e; exact crit_sig h1 h2
  -- registrations: no new one unless `t` registers from its load
  have hnr : (∀ u, (C.ph (G' u)).isReg = true → (C.ph (G u)).isReg = true) ∨
      (∃ i e, C.ph (G t) = .ld i e) := by
    by_cases hr : (C.ph (G t)).isReg = true
    · exact .inl fun u hr' => by
        by_cases e : u = t
        · subst e; exact hr
        · rwa [hcu u e] at hr'
    · by_cases hr' : p.isReg = true
      · obtain ⟨i, jr, sn, e, rfl⟩ := CPh.isReg_eq hr'
        cases hc : C.ph (G t) with
        | ld i' e' => exact .inr ⟨i', e', rfl⟩
        | reg _ _ _ _ => rw [hc] at hr; exact absurd rfl hr
        | _ => rw [hc] at hn; cases hn
      · exact .inl fun u hr'' => by
          by_cases e : u = t
          · subst e; rw [hct] at hr''; exact absurd hr'' hr'
          · rwa [hcu u e] at hr''
  -- no registration of `t` while another thread is registered (`rc`)
  have hnr1 : ∀ u, u ≠ t → (C.ph (G u)).isReg = true →
      ∀ v, (C.ph (G' v)).isReg = true → (C.ph (G v)).isReg = true := fun u _ hu => by
    rcases hnr with hnr | ⟨_, _, e'⟩
    · exact hnr
    · exact (hw.rc u t hu (by rw [e']; rfl)).elim
  have hld : ∀ i e, p = .ld i e → C.ph (G t) = .en → (C.Ep.hist m).size = i + 1 ∧
      C.Ep.hist m' = C.Ep.hist m := fun i e hp hen => by
    obtain ⟨hi, hh⟩ := ld_newest hw.ehb hphl hphp hst hI hen (by rw [hct, hp])
    have hlt : i < (C.Ep.hist m').size := (hI'.ld t i e (by rw [hct, hp])).1
    rw [hh] at hlt
    exact ⟨by omega, hh⟩
  -- at most one registered waiter after the step
  have hone : ∀ u v, (C.ph (G' u)).isReg = true → (C.ph (G' v)).isReg = true → u = v := by
    rcases hnr with hnr | ⟨i₀, e₀, e'⟩
    · exact fun u v hu hv => hw.one u v (hnr u hu) (hnr v hv)
    · -- `t` registers from its load, so no other thread is registered
      have ht : ∀ u, (C.ph (G' u)).isReg = true → u = t := fun u hu => by
        by_cases e : u = t
        · exact e
        · rw [hcu u e] at hu; exact (hw.rc u t hu (by rw [e']; rfl)).elim
      exact fun u v hu hv => (ht u hu).trans (ht v hv).symm
  refine ⟨hone, hw.ehb.step hhb ?_, fun u i e h' => ?_, fun u v hr hc => ?_,
    fun u i jr sn e h' => ?_, fun u i jr sn e v q' n h' hu' hv => ?_,
    fun u i jr sn e h' hsz => ?_, fun v q' n h' hv => ?_⟩
  · -- ehb: the new epoch write is the holder's
    rcases hEw with e | ⟨⟨q₀, n₀, h₀, e⟩, -, x, hx, e'⟩
    · exact .inl e
    · exact .inr ⟨x, e', FLock.HB.of_holder (t := t)
        (hheld t (LPh.held_of_holds (hsh t (by rw [e]; rfl))))
        (by rw [hx]; exact VClock.le_refl _)⟩
  · -- f0
    by_cases et : u = t
    · subst et
      rw [hct] at h'
      subst h'
      cases hc : C.ph (G u) with
      | en => rw [(hld i e rfl hc).2]; exact (hld i e rfl hc).1
      | ld i₀ e₀ =>
        rw [hc] at hn
        have hn2 : CPh.ld i₀ e₀ = CPh.ld i e := hn
        cases hn2
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e']; exact hw.f0 u _ _ hc
        · rw [hc] at e'; cases e'
      | _ => have hcr := hn.crit rfl; rw [hc] at hcr; cases hcr
    · rw [hcu u et] at h'
      rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
      · rw [e']; exact hw.f0 u i e h'
      · exact (hcp u t (by rw [h']; rfl) (hincE _ _ _ e')).elim
  · -- rc
    by_cases eu : u = t
    · subst eu
      by_cases ev : v = u
      · subst ev; rw [hct] at hr hc
        obtain ⟨_, _, _, _, rfl⟩ := CPh.isReg_eq hr; cases hc
      · rw [hcu v ev] at hc; rw [hct] at hr
        cases hr0 : (C.ph (G u)).isReg
        · exact ev (hI.crit1 v u hc (hn.crit_of_reg hr (by simpa using hr0)))
        · exact hw.rc u v hr0 hc
    · rw [hcu u eu] at hr
      by_cases ev : v = t
      · subst ev; rw [hct] at hc; exact hw.rc u v hr (hn.crit hc)
      · rw [hcu v ev] at hc; exact hw.rc u v hr hc
  · -- f2
    by_cases et : u = t
    · subst et
      rw [hct] at h'
      rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
      · rw [e']
        rw [h'] at hn
        cases hc : C.ph (G u) with
        | ld i₀ e₀ =>
          rw [hc] at hn; obtain ⟨rfl, -, -⟩ := hn
          have := hw.f0 u _ _ hc; omega
        | reg i₀ jr₀ sn₀ e₀ =>
          rw [hc] at hn; obtain ⟨-, hi⟩ := hn
          have := hw.f2 u i₀ jr₀ sn₀ e₀ hc; omega
        | _ => rw [hc] at hn; cases hn
      · rw [e'] at hn; rw [h'] at hn; cases hn
    · rw [hcu u et] at h'
      rcases hEw with e' | ⟨⟨q₀, n₀, h₀, e'⟩, hsz, -⟩
      · rw [e']; exact hw.f2 u i jr sn e h'
      · have := hw.f3 u i jr sn e t q₀ n₀ h₀ h' e'; omega
  · -- f3
    by_cases et : u = t
    · subst et
      rw [hct] at hu'
      have hvt : v ≠ u := fun e => by subst e; rw [hct] at hv; rw [hu'] at hv; cases hv
      rw [hcu v hvt] at hv
      rw [hu'] at hn
      cases hc : C.ph (G u) with
      | ld i₀ e₀ => exact (hcp u v (by rw [hc]; rfl) (by rw [hv]; rfl)).elim
      | reg i₀ jr₀ sn₀ e₀ =>
        rw [hc] at hn; obtain ⟨-, hi⟩ := hn
        have := hw.f3 u i₀ jr₀ sn₀ e₀ v q' n h' hc hv
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e']; omega
        · rw [hc] at e'; cases e'
      | _ => rw [hc] at hn; cases hn
    · rw [hcu u et] at hu'
      by_cases ev : v = t
      · subst ev
        rw [hct] at hv
        rw [hv] at hn
        rcases hn.to_inc with ⟨sh, c, hc⟩ | hc
        · -- `t`'s post: the epoch has at most one write after `u`'s saved one, else the state
          -- write before it is sated (`f4`), and no post follows a sated write
          have hpf := post_facts hI hI' hG hc (by rw [hct, hv]) (by rw [hct]; exact hsg)
          have hE : C.Ep.hist m' = C.Ep.hist m := by
            rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
            · exact e'
            · rw [hc] at e'; cases e'
          rw [hE]
          have h2 := hw.f2 u i jr sn e hu'
          exact Classical.byContradiction fun hne => hpf.1 (hw.f4 u i jr sn e hu' (by omega))
        · have := hw.f3 u i jr sn e v q' n h' hu' hc
          rcases hEp with e' | ⟨_, _, _, -, ep⟩
          · rw [e']; exact this
          · rw [hv] at ep; cases ep
      · rw [hcu v ev] at hv
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e']; exact hw.f3 u i jr sn e v q' n h' hu' hv
        · exact absurd (hsig1 v t (by rw [hv]; rfl) (hincE _ _ _ e')) ev
  · -- f4
    by_cases et : u = t
    · subst et
      rw [hct] at h'
      rw [h'] at hn
      cases hc : C.ph (G u) with
      | ld i₀ e₀ =>
        rw [hc] at hn; obtain ⟨rfl, -, -⟩ := hn
        have := hw.f0 u _ _ hc
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e'] at hsz; omega
        · rw [hc] at e'; cases e'
      | reg i₀ jr₀ sn₀ e₀ =>
        rw [hc] at hn; obtain ⟨-, hi⟩ := hn
        have hE : C.Ep.hist m' = C.Ep.hist m := by
          rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
          · exact e'
          · rw [hc] at e'; cases e'
        rw [hE] at hsz
        have h2 := hw.f2 u i₀ jr₀ sn₀ e₀ hc
        exact Sated.keep hI hI' (hnr1 u (by omega) (by rw [hc]; rfl) |>.elim id id) hSh
          (hw.f4 u i₀ jr₀ sn₀ e₀ hc (by omega))
      | _ => rw [hc] at hn; cases hn
    · rw [hcu u et] at h'
      have hnr' := hnr1 u et (by rw [h']; rfl)
      rcases hEw with e' | ⟨⟨q₀, n₀, h₀, e'⟩, -, -⟩
      · rw [e'] at hsz; exact Sated.keep hI hI' hnr' hSh (hw.f4 u i jr sn e h' hsz)
      · exact Sated.keep hI hI' hnr' hSh (hw.incS t q₀ n₀ h₀ e')
  · -- incS
    by_cases ev : v = t
    · subst ev
      rw [hct] at hv
      rw [hv] at hn
      rcases hn.to_inc with ⟨sh, c, hc⟩ | hc
      · -- `t`'s post, with at most one registered waiter
        exact (post_facts hI hI' hG hc (by rw [hct, hv]) (by rw [hct]; exact hsg)).2.1
          (wOf_le_one hI' hone)
      · have hnr' : ∀ u, (C.ph (G' u)).isReg = true → (C.ph (G u)).isReg = true := by
          rcases hnr with hnr | ⟨_, _, e'⟩
          · exact hnr
          · rw [hc] at e'; cases e'
        exact Sated.keep hI hI' hnr' hSh (hw.incS v q' n h' hc)
    · rw [hcu v ev] at hv
      have hnr' : ∀ u, (C.ph (G' u)).isReg = true → (C.ph (G u)).isReg = true := by
        rcases hnr with hnr | ⟨_, _, e'⟩
        · exact hnr
        · exact (hcp t v (by rw [e']; rfl) (by rw [hv]; rfl)).elim
      exact Sated.keep hI hI' hnr' hSh (hw.incS v q' n h' hv)

end FCond

namespace FSem

variable {γ Y : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ Y L C}

/-- **`Win1` over a step of the semaphore's primitive** (`FLock.Fits.kstep` of `FSem.prim`):
a step of the condition's code (`FCond.Win1.step`; a thread in the signal code is at `pst` and
holds the mutex: `FCond.Inv.sx`, `FSem.sx_iff`, `FSem.Inv.pst`), the waiter's entry into the
condition's wait (`FCond.Win1.enter`, when the client's `hent` gives that no waiter is registered
then) or the holder's step on the mutex's resource (the same places and the condition's writes,
`FCond.hist_hold`). `hphl`, `hphp`, `hlph`: the laws of the semaphore's places next to the mutex
(`FLock.Fits.ph_l`, `ph_part`, `lph`); `hap`: the condition's words are apart from the mutex's. -/
theorem Win1.semStep {G G' : ThreadId → γ} {rX rX' : Res} {m m' : Mem} {t : ThreadId}
    (hw : C.Win1 L G m) (hsub : S.prim.Sub G rX m)
    (hphl : ∀ g q h, S.place.ph (L.set g q h) = S.place.ph g)
    (hphp : ∀ g r, S.place.ph (L.setPart g r) = S.place.ph g)
    (hlph : ∀ g q, L.ph (S.place.set g q) = L.ph g)
    (hap : ∀ W, (W = C.S ∨ W = C.Ep) → W.ApartL L.toLockWord)
    (hent : S.cnt G = 0 → S.ph (G t) = .wt → S.wx (G t) → C.ph (G t) = .out →
      ∀ u, (C.ph (G u)).isReg = false)
    (hst : S.prim.Step t G rX m G' rX' m') : C.Win1 L G' m' := by
  have hcl : ∀ g q h, C.ph (L.set g q h) = C.ph g := fun g q h => congrArg Prod.fst (hphl g q h)
  have hcp : ∀ g r, C.ph (L.setPart g r) = C.ph g := fun g r => congrArg Prod.fst (hphp g r)
  obtain ⟨-, hs | ⟨-, hmv⟩⟩ := hst
  · exact hw.step hsub.1 (fun u hu => hsub.2.pst u ((S.sx_iff _).mp (hsub.1.1.sx u hu)))
      hcl hcp hap hs
  cases hmv with
  | enter _ hct hst hwx hcnt =>
    have hlc : ∀ u, L.ph (upd G t (C.set (G t) .en) u) = L.ph (G u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, ← S.place_c, hlph]
      · rw [upd_ne _ _ e]
    exact hw.enter (by rw [upd_self, C.ph_set]) (fun u e => by rw [upd_ne _ _ e])
      (hent hcnt hst hwx hct)
      (hw.ehb.step (fun _ hc => hc.mono (fun u hu => .inl (by rw [hlc]; exact hu))
        (fun _ => VClock.le_refl _) (fun _ h => h) rfl fun u hg => by rwa [hlc] at hg) (.inl rfl))
  | hold s h hlt _ hL _ hfs _ hcells _ =>
    have hfs' := hfs.cells
    have hls : ∀ g s, L.ph (S.set g s) = L.ph g := fun g s => by rw [← S.place_s, hlph]
    have hlc : ∀ u, L.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = L.ph (G u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, hls, L.ph_set, hlt]
      · rw [upd_ne _ _ e]
    have hE := FCond.hist_hold hsub.1 hfs' hcells (.inr rfl)
    exact hw.keep (fun u => by
        by_cases e : u = t
        · subst e; rw [upd_self, S.cph_set, hcl]
        · rw [upd_ne _ _ e])
      (FCond.hist_hold hsub.1 hfs' hcells (.inl rfl)) hE
      (hw.ehb.step (fun _ hc => hc.mono (fun u hu => .inl (by rw [hlc]; exact hu)) hfs'.clock
        (hL.before_fstep hfs') hfs'.threads fun u hg => by rwa [hlc] at hg) (.inl hE))

end FSem

end Full
end Zig
