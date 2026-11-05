import Proofs.SemCounter.Mem

/-!
# The steps of `semaphoreCounter`'s protocol

The rest `U` (`Proofs/SemCounter/Protocol.lean`) over every step the protocol with the semaphore
admits (`FSem.Fits`): a step of the lock's code (`stable`), a stop (`atStop`), a caller-part tick
(`tickStable`), a step of the condition's code (`cstep` at a word, `U_own` on the thread's own
part), and a step of the semaphore's own code (`FSem.Move`: the entry into the condition's wait,
`U_enter`; the holder's step on the mutex's resource, `U_hold`).

The client's part `Lg`: the places of the threads in the program (`X.ph`) give `one`, `tot` and
`wtx`; the window's facts (`ehb`, `f0`, `rc`, `f2`, `f3`, `f4`, `incS`) read the places in the
condition's code and the condition's writes, and move only at the condition's steps that make
them (`cstep`).
-/

namespace Zig
namespace SemCounter

open Conc Conc.Proto Full Full.FAssn

/-! ## The ghost values -/

theorem xs_upd {G : ThreadId → Gh} {t : ThreadId} {g : Gh} (h : g.2.ph = (G t).2.ph) :
    xs (upd G t g) = xs G := by
  funext u; unfold xs upd; split
  · rename_i e; subst e; exact h
  · rfl

/-- A thread in the semaphore's code is thread 0 or 1. -/
theorem lt2 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : UM G rX m) (hI : S.Inv G m)
    {u : ThreadId} (h : (G u).2.sp ≠ .out) : u < 2 := by
  have := hI.ex u h
  obtain ⟨-, ⟨hs, -⟩ | ⟨hs, -⟩⟩ := hu.shape <;> (unfold ThreadId at *; omega)

/-- `HB` over a step that keeps every thread's lock place, the memory's clocks, the lock's word and
the threads. -/
theorem hb_same {G G' : ThreadId → Gh} {m : Mem} (hph : ∀ u, (G' u).1.ph = (G u).1.ph)
    {c : VClock} (h : L.HB G m c) : L.HB G' m c :=
  h.mono (fun u hu => .inl (by show ((G' u).1.ph).held = true; rw [hph u]; exact hu)) (fun _ => VClock.le_refl _) (fun _ h => h) rfl
    (fun u hg => by
      show (G u).1.ph ≠ .gone
      rw [← hph u]; exact hg)

/-- `HB` over a framed step with the lock's word and the rest in its frame (`FStepIn`) that keeps
every thread's lock place. -/
theorem hb_fstep {G G' : ThreadId → Gh} {rX : Res} {m m' : Mem} (hL : L.Inv G rX m)
    (hs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') (hph : ∀ u, (G' u).1.ph = (G u).1.ph)
    {c : VClock} (h : L.HB G m c) : L.HB G' m' c :=
  h.mono (fun u hu => .inl (by show ((G' u).1.ph).held = true; rw [hph u]; exact hu)) hs.clock (hL.before_fstep hs) hs.threads
    (fun u hg => by
      show (G u).1.ph ≠ .gone
      rw [← hph u]; exact hg)

/-- **`Lg` over a step that keeps every thread's place in the condition's code and the
condition's writes**, with the permit's facts, `wtx` and `ehb` after it given. -/
theorem Lg.relabel {G G' : ThreadId → Gh} {m m' : Mem} (hl : Lg G m)
    (hc : ∀ u, (G' u).2.c = (G u).2.c) (hS : WS.hist m' = WS.hist m) (hE : WE.hist m' = WE.hist m)
    (one : (G' 0).2.ph.holds = false ∨ (G' 1).2.ph.holds = false)
    (tot : ∀ u k s, (G' u).2.ph = .work k true s → s = sum (xs G'))
    (wtx : ∀ u, (G' u).2.sp = .wt → Wx (G' u).2.ph) (ehb : L.WordHB WE G' m') : Lg G' m' := by
  have hsat : C.Sated m' ↔ C.Sated m := FCond.Sated.congr (C := C) hS
  exact ⟨one, tot, wtx, ehb,
    fun u i e h => by rw [hc u] at h; rw [hE]; exact hl.f0 u i e h,
    fun u v hr hc' => by rw [hc u] at hr; rw [hc v] at hc'; exact hl.rc u v hr hc',
    fun u i jr sn e h => by rw [hc u] at h; rw [hE]; exact hl.f2 u i jr sn e h,
    fun u i jr sn e v q n h hu hv => by
      rw [hc u] at hu; rw [hc v] at hv; rw [hE]; exact hl.f3 u i jr sn e v q n h hu hv,
    fun u i jr sn e h hs => by
      rw [hc u] at h; rw [hE] at hs; exact hsat.mpr (hl.f4 u i jr sn e h hs),
    fun v q n h hv => by rw [hc v] at hv; exact hsat.mpr (hl.incS v q n h hv)⟩

/-- **`Lg` over a step that keeps every thread's place in the program and in the condition's code
and the condition's writes**, with `wtx` and `ehb` after it given. -/
theorem Lg.congr {G G' : ThreadId → Gh} {m m' : Mem} (hl : Lg G m)
    (hph : ∀ u, (G' u).2.ph = (G u).2.ph) (hc : ∀ u, (G' u).2.c = (G u).2.c)
    (hS : WS.hist m' = WS.hist m) (hE : WE.hist m' = WE.hist m)
    (wtx : ∀ u, (G' u).2.sp = .wt → Wx (G' u).2.ph) (ehb : L.WordHB WE G' m') : Lg G' m' :=
  hl.relabel hc hS hE (by rw [hph 0, hph 1]; exact hl.one)
    (fun u k s h => by
      rw [hph u] at h; rw [show xs G' = xs G from funext hph]; exact hl.tot u k s h) wtx ehb

/-! ## The lock's steps and the stops -/

/-- **A step of the lock's code keeps `U`** (`FLock.Fits.stable`). -/
theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hok : ok (G t)) (hg : L.ph (G t) ≠ .gone) (hna : L.ph (G t) ≠ .away)
    (hz : L.ph (G t) ≠ .holdsAway) (hu : U G rX m) (hs : L.Step t m m')
    (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) rX m' := by
  have hX : ∀ u, (upd G t (L.set (G t) p h) u).2 = (G u).2 := fun u =>
    congrFun (FLock.snd_set G t p h) u
  have hst : (S.ph (G t)).isPst = false := by
    rcases hok.2 with e | e <;> (show (G t).2.sp.isPst = false; rw [e]; rfl)
  refine ⟨hu.um.lstep hs (funext fun u => congrArg X.ph (hX u)),
    hu.cinv.lstep hu.um.ws hu.um.we apS apE hok.1 hna (fun _ _ _ => rfl) hs,
    hu.sinv.lstep hu.um.ws apS (fun _ _ _ => rfl) (fun _ _ _ => rfl) hst hg hz hs hrel,
    hu.lg.congr (fun u => congrArg X.ph (hX u)) (fun u => congrArg X.c (hX u))
      (hu.um.ws.lockStep hs apS).2 (hu.um.we.lockStep hs apE).2
      (fun u h' => by rw [hX u] at h' ⊢; exact hu.lg.wtx u h')
      (hu.lg.ehb.lstep hu.um.we apE hg hz hs hrel)⟩

/-- A stop keeps `U`: it reads no current thread. -/
theorem atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : U G rX m) :
    U G rX { m with current := t } :=
  ⟨hu.um.atStop t,
    hu.cinv.stay (m' := { m with current := t }) rfl rfl rfl (fun _ hw _ => hw) (fun _ _ h => h)
      (Nat.le_refl _) (fun _ => VClock.le_refl _),
    hu.sinv.mono (m' := { m with current := t }) (fun _ => rfl) (fun _ => rfl) rfl hu.sinv.pst
      (fun _ h => .inl h) (fun _ => VClock.le_refl _) (fun _ h => h) rfl (fun _ h => h)
      (fun _ h => .inl h) rfl,
    ⟨hu.lg.one, hu.lg.tot, hu.lg.wtx, hu.lg.ehb, hu.lg.f0, hu.lg.rc, hu.lg.f2, hu.lg.f3, hu.lg.f4,
      hu.lg.incS⟩⟩

/-! ## The steps on a thread's own part and on the mutex's resource -/

/-- **A framed step of `t` on its own part keeps `U`** (a tick, a step of the condition's code on
`t`'s own part): the same places, the new part's ghost value `g`, the lock's invariant after it,
and the condition's and the semaphore's invariants after it. -/
theorem U_own {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {W : Word 32 4} (hW2 : Two W) (hu : U G (rsum (W.cellsR m) rY) m)
    (hi : L.Inv G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m')
    (hw' : W.Ok m') (hh : W.hist m' = W.hist m)
    (hi' : L.Inv (upd G t g) (rsum (W.cellsR m') rY) m') (hX : g.2 = (G t).2)
    (hph : g.1.ph = (G t).1.ph)
    (hci : C.Inv L (upd G t g) m') (hsi : S.Inv (upd G t g) m') :
    U (upd G t g) (rsum (W.cellsR m') rY) m' := by
  have hX' : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hX]
    · rw [upd_ne _ _ e]
  have hP' : ∀ u, (upd G t g u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  obtain ⟨hum, hhS, hhE⟩ := UM_own_native hW2 hu.um hY hs hw' hh hi'
    (funext fun u => congrArg X.ph (hX' u))
  exact ⟨hum, hci, hsi, hu.lg.congr (fun u => congrArg X.ph (hX' u))
    (fun u => congrArg X.c (hX' u)) hhS hhE
    (fun u h' => by rw [hX' u] at h' ⊢; exact hu.lg.wtx u h')
    (hu.lg.ehb.step (fun _ hc => hb_fstep hi hs hP' hc) (.inl hhE))⟩

/-- **A tick of the caller's part keeps `U`** (`FLock.Fits.kstep`'s `PartTick`). -/
theorem tickStable (t : ThreadId) (G : ThreadId → Gh) (rX : Res) (m : Mem)
    (G' : ThreadId → Gh) (rX' : Res) (m' : Mem)
    (hs : L.PartTick t G rX m G' rX' m') (hu : U G rX m) : U G' rX' m' := by
  have hsi := hu.sinv.partTick (fun _ _ => rfl) (fun _ _ => rfl) hs
  obtain ⟨hc, _, hi, r, _, rfl, rfl, rfl, hi'⟩ := hs
  obtain ⟨rY, hrX, hY⟩ := Rest.split (fun _ => ws_box) hu.um.rest
  subst hrX
  have hfs := FStepIn.ticked m (rsum (L.wordR m) (rsum (WS.cellsR m) rY)).heap.erase
  have hS : WS.hist m.ticked = WS.hist m :=
    Word.hist_fstep hu.um.ws hfs
      (fun l hl => frame_rest (rest_box hu.um.rest (fun _ => box_live hu.um) (ws_box hl)))
      (fun l _ => rfl)
  have hE : WE.hist m.ticked = WE.hist m :=
    Word.hist_fstep hu.um.we hfs
      (fun l hl => frame_rest (rest_box hu.um.rest (fun _ => box_live hu.um) (we_box hl)))
      (fun l _ => rfl)
  have hci : C.Inv L (upd G t (L.setPart (G t) r)) m.ticked :=
    hu.cinv.other rfl (fun _ => rfl) (fun _ h => h) id hS hE (by rw [hfs.waiters])
      (fun w hw _ => .inl (by rw [hfs.waiters] at hw; exact hw))
      (fun _ _ _ h => by rw [hfs.woken]; exact h) (Nat.le_of_eq (by rw [hfs.threads])) hfs.clock
  have hcl : m.ticked = { m with ticks := m.ticks + 1 } := rfl
  exact U_own (.inl rfl) hu hi hY hfs (by rw [hcl]; exact hu.um.ws.ticked) hS hi' rfl rfl hci hsi

/-- **The holder's step on the mutex's resource keeps `U`** (`FSem.Move.hold`): the same places
in the program and in the condition's code, the semaphore's place by `Go`, the condition's words
kept (the extent in the rest pins the `SemCounter`). -/
theorem U_hold {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {s : SPh} {h : Res}
    (hu : U G rX m) (hL : L.Inv G rX m)
    (hs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') (hL' : ∃ G'', L.Inv G'' rX m')
    (hgo : S.Go G m t s) (hlt : L.ph (G t) = .holds)
    (hci : C.Inv L (upd G t (S.set (L.set (G t) .holds h) s)) m')
    (hsi : S.Inv (upd G t (S.set (L.set (G t) .holds h) s)) m') :
    U (upd G t (S.set (L.set (G t) .holds h) s)) rX m' := by
  obtain ⟨G'', hL''⟩ := hL'
  have hph : ∀ u, (upd G t (S.set (L.set (G t) .holds h) s) u).2.ph = (G u).2.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hc : ∀ u, (upd G t (S.set (L.set (G t) .holds h) s) u).2.c = (G u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hP' : ∀ u, (upd G t (S.set (L.set (G t) .holds h) s) u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; exact hlt.symm
    · rw [upd_ne _ _ e]
  obtain ⟨hum, hhS, hhE⟩ := UM_stepIn hu.um hs hL'' (funext hph)
  refine ⟨hum, hci, hsi, hu.lg.congr hph hc hhS hhE (fun u h' => ?_)
    (hu.lg.ehb.step (fun _ hc => hb_fstep hL hs hP' hc) (.inl hhE))⟩
  by_cases e : u = t
  · subst e
    rw [upd_self] at h' ⊢
    have h's : s = .wt := h'
    rcases hgo with e | ⟨-, -, hwx⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact hu.lg.wtx u (e.symm.trans h's)
    · exact hwx
    · rw [h's] at e; cases e
    · rw [h's] at e; cases e
  · rw [upd_ne _ _ e] at h' ⊢; exact hu.lg.wtx u h'

/-! ## The entry into the condition's wait -/

/-- No thread has the permit while two threads without it are in the semaphore's code. -/
theorem cnt_ne {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : UM G rX m) (hI : S.Inv G m)
    {u v : ThreadId} (huv : u ≠ v) (hu' : (G u).2.sp ≠ .out) (hv' : (G v).2.sp ≠ .out)
    (hxu : Wx (G u).2.ph) (hxv : Wx (G v).2.ph) : S.cnt G ≠ 0 := by
  have h1 := lt2 hu hI hu'
  have h2 := lt2 hu hI hv'
  obtain ⟨k, s, -, eu⟩ := hxu
  obtain ⟨k', s', -, ev⟩ := hxv
  have hh : held (xs G) = false := by
    unfold held xs
    rcases (by unfold ThreadId at *; omega : u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [eu, ev, Ph.holds]
  show pv (xs G) ≠ 0
  unfold pv; rw [hh]; decide

/-- **The waiter's entry into the condition's wait keeps `U`** (`FSem.Move.enter`): no thread is
registered (the count is 0, so the permit's holder runs, and the two threads without it are the
waiter and a registered one). -/
theorem U_enter {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} (hu : U G rX m)
    (hct : C.ph (G t) = .out) (hst : S.ph (G t) = .wt) (hwx : S.wx (G t)) (hcnt : S.cnt G = 0)
    (hci : C.Inv L (upd G t (C.set (G t) .en)) m) (hsi : S.Inv (upd G t (C.set (G t) .en)) m) :
    U (upd G t (C.set (G t) .en)) rX m := by
  have hct' : (G t).2.c = .out := hct
  have hph : ∀ u, (upd G t (C.set (G t) .en) u).2.ph = (G u).2.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hsp : ∀ u, (upd G t (C.set (G t) .en) u).2.sp = (G u).2.sp := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hP : ∀ u, (upd G t (C.set (G t) .en) u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; rfl
    · rw [upd_ne _ _ e]
  have hct2 : (upd G t (C.set (G t) .en) t).2.c = .en := by rw [upd_self]; rfl
  -- a thread at another place in the condition's code than `en` is not `t`
  have hne : ∀ u, (upd G t (C.set (G t) .en) u).2.c ≠ .en →
      (upd G t (C.set (G t) .en) u).2.c = (G u).2.c := fun u h => by
    by_cases e : u = t
    · subst e; exact absurd hct2 h
    · rw [upd_ne _ _ e]
  have hum : UM (upd G t (C.set (G t) .en)) rX m :=
    ⟨by rw [xs_upd (g := C.set (G t) .en) rfl]; exact hu.um.shape, hu.um.io, hu.um.rest, hu.um.blk, hu.um.ws, hu.um.we,
      hu.um.q⟩
  refine ⟨hum, hci, hsi, ⟨by rw [hph 0, hph 1]; exact hu.lg.one, fun u k s h => ?_,
    fun u h => by rw [hsp u] at h; rw [hph u]; exact hu.lg.wtx u h,
    fun k hk => hb_same hP (hu.lg.ehb k hk),
    fun u i e h => by
      rw [hne u (by rw [h]; nofun)] at h; exact hu.lg.f0 u i e h,
    fun u v hr hc => ?_,
    fun u i jr sn e h => by
      rw [hne u (by rw [h]; nofun)] at h; exact hu.lg.f2 u i jr sn e h,
    fun u i jr sn e v q n h hu' hv => by
      rw [hne u (by rw [hu']; nofun)] at hu'; rw [hne v (by rw [hv]; nofun)] at hv
      exact hu.lg.f3 u i jr sn e v q n h hu' hv,
    fun u i jr sn e h hs => by
      rw [hne u (by rw [h]; nofun)] at h; exact hu.lg.f4 u i jr sn e h hs,
    fun v q n h hv => by
      rw [hne v (by rw [hv]; nofun)] at hv; exact hu.lg.incS v q n h hv⟩⟩
  · rw [hph u] at h; rw [xs_upd (g := C.set (G t) .en) rfl]; exact hu.lg.tot u k s h
  · -- `u` registered, `v` in the critical code
    have hut : u ≠ t := fun e => by subst e; rw [hct2] at hr; cases hr
    rw [upd_ne _ _ hut] at hr
    by_cases e : v = t
    · subst e
      -- `u` waits in the semaphore's wait, without the permit, as does `v`
      have hw : (G u).2.sp = .wt := hu.sinv.wt u (by
        show ((G u).2.c).waits = true
        obtain ⟨i, jr, sn, e', he⟩ := CPh.isReg_eq hr; rw [he]; rfl)
      exact cnt_ne hu.um hu.sinv hut (by rw [hw]; nofun) (by rw [show (G v).2.sp = .wt from hst]; nofun)
        (hu.lg.wtx u hw) hwx hcnt
    · rw [upd_ne _ _ e] at hc; exact hu.lg.rc u v hr hc

/-! ## The condition's writes -/

/-- The newest `waiters` does not rise when no thread becomes registered (`FCond.Inv.cnt`). -/
theorem wle {G G' : ThreadId → Gh} {m m' : Mem} (hI : C.Inv L G m) (hI' : C.Inv L G' m')
    (h : ∀ u, ((G' u).2.c).isReg = true → ((G u).2.c).isReg = true) :
    FCond.wOf (C.lastS m') ≤ FCond.wOf (C.lastS m) := by
  obtain ⟨T, hT, hw, -⟩ := hI.cnt
  obtain ⟨T', hT', hw', -⟩ := hI'.cnt
  rw [hw, hw', ← FCond.nreg_ext hT (Nat.le_max_left T T'),
    ← FCond.nreg_ext hT' (Nat.le_max_right T T')]
  exact tsum_le fun u _ => by
    show (if ((G' u).2.c).isReg then 1 else 0) ≤ (if ((G u).2.c).isReg then 1 else 0)
    cases h1 : ((G' u).2.c).isReg
    · simp
    · simp [h u h1]

/-- At most one waiter when only thread `v` may be registered. -/
theorem wle1 {G : ThreadId → Gh} {m : Mem} (hI : C.Inv L G m) (v : ThreadId)
    (h : ∀ u, ((G u).2.c).isReg = true → u = v) : FCond.wOf (C.lastS m) ≤ 1 := by
  obtain ⟨T, hT, hw, -⟩ := hI.cnt
  rw [hw, ← FCond.nreg_ext hT (Nat.le_max_left T (v + 1))]
  calc C.nreg G (Max.max T (v + 1))
      ≤ tsum (Max.max T (v + 1)) (fun u => if u = v then 1 else 0) := tsum_le fun u _ => by
        show (if ((G u).2.c).isReg then 1 else 0) ≤ _
        cases h1 : ((G u).2.c).isReg
        · simp
        · simp [h u h1]
    _ = 1 := tsum_point (by omega) 1

/-- **`signals = waiters` stays** over a step with the condition's invariant after it in which no
thread becomes registered: the state's writes are kept or get one that registers no thread. -/
theorem sated_keep {G G' : ThreadId → Gh} {m m' : Mem} (hI : C.Inv L G m) (hI' : C.Inv L G' m')
    (hnr : ∀ u, ((G' u).2.c).isReg = true → ((G u).2.c).isReg = true)
    (hS : WS.hist m' = WS.hist m ∨ ∃ x, WS.hist m' = (WS.hist m).push x)
    (hs : C.Sated m) : C.Sated m' := by
  rcases hS with e | ⟨x, e⟩
  · exact (FCond.Sated.congr (C := C) e).mpr hs
  · refine hI'.sated_push hI.spos e hs ?_
    rw [← FCond.lastS_push (C := C) e]; exact wle hI hI' hnr

/-- A thread in the signal code is at `pst` (`FCond.Inv.sx`, `FSem.sx_iff`). -/
theorem sig_pst {G : ThreadId → Gh} {m : Mem} (hI : C.Inv L G m) {u : ThreadId}
    (h : ((G u).2.c).sig = true) : ((G u).2.sp).isPst = true := hI.sx u h

/-- A thread in the signal code holds the mutex (`FSem.Inv.pst`). -/
theorem sig_holds {G : ThreadId → Gh} {m : Mem} (hI : C.Inv L G m) (hsi : S.Inv G m)
    {u : ThreadId} (h : ((G u).2.c).sig = true) : (G u).1.ph = .holds :=
  hsi.pst u (sig_pst hI h)

/-- **A post** (`sl → inc` of `t`): the state's new write raises `signals` (`SigStep.inc_fresh`)
and registers no thread, so it does not follow a sated write, and with at most one waiter it is
sated. -/
theorem post_facts {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g' : Gh}
    {sh : Array Word.Entry} {c : VClock} {q n : Nat} {h : Array Word.Entry}
    (hI : C.Inv L G m) (hI' : C.Inv L (upd G t g') m')
    (ht : (G t).2.c = .sl sh c) (ht' : g'.2.c = .inc q n h)
    (hsg : C.SigStep t (C.ph (G t)) (C.ph (upd G t g' t)) m m') :
    ¬ C.Sated m ∧ (FCond.wOf (C.lastS m') ≤ 1 → C.Sated m') ∧
      ∃ x, WS.hist m' = (WS.hist m).push x := by
  have ht'' : C.ph (upd G t g' t) = .inc q n h := by rw [upd_self]; exact ht'
  obtain ⟨hq, ⟨x, hx⟩, -, hq0, hlt⟩ := FCond.SigStep.inc_fresh (C := C) ht ht''
    (fun u hu => upd_ne _ _ hu) hsg hI hI'
  have hlast' : C.lastS m' = (C.S.hist m')[q]! := by
    rw [FCond.lastS_push (C := C) hx, hx, hq]; exact Word.get_push_eq.symm
  have hlast : C.lastS m = (C.S.hist m')[q - 1]! := by
    have := hI.spos; unfold FCond.lastS; rw [hx, hq]; exact (Word.get_push_lt (by omega)).symm
  have hnr : ∀ u, ((upd G t g' u).2.c).isReg = true → ((G u).2.c).isReg = true := fun u hr => by
    by_cases e : u = t
    · subst e; rw [upd_self, ht'] at hr; cases hr
    · rwa [upd_ne _ _ e] at hr
  have hw := wle hI hI' hnr
  have hsv := (hI'.sv q (by rw [hx, hq, Array.size_push]; omega)).2
  rw [← hlast'] at hsv
  rw [← hlast', ← hlast] at hlt
  refine ⟨fun hs => ?_, fun h1 => ?_, x, hx⟩
  · unfold FCond.Sated at hs; omega
  · unfold FCond.Sated; omega

/-! ## A step of the condition's code -/

/-- **A step of the condition's code at one of its words keeps `U`** (`FLock.Fits.kstep` of
`FSem.prim`, its condition's steps; module doc). -/
theorem cstep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : CPh) (q : LPh)
    (h : Res) (W : Word 32 4) (hW : W = C.S ∨ W = C.Ep)
    (hn : CPh.Next (C.ph (G t)) p)
    (hq : (q = L.ph (G t) ∧ h = L.held (G t)) ∨
      ((L.ph (G t) = .out ∨ (L.ph (G t) = .away ∧ (C.ph (G t)).isReg = true)) ∧
        (q = .out ∨ (q = .away ∧ p.waits = true)) ∧ h = rnil))
    (hu : U G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : C.MStep W t m m')
    (hEp : C.Ep.hist m' = C.Ep.hist m ∨ ∃ q n h, C.ph (G t) = .inc q n h ∧ p = .wk n q h)
    (hsg : C.SigStep t (C.ph (G t)) p m m') (hWI : L.WInv (L.pl G) m)
    (hI : C.Inv L (upd G t (L.set (C.set (G t) p) q h)) m')
    (hsi : S.Inv (upd G t (L.set (C.set (G t) p) q h)) m') :
    U (upd G t (L.set (C.set (G t) p) q h)) (rsum (W.cellsR m') rY) m' := by
  have hW2 : Two W := hW
  -- what the step does to the memory (`FCond.MStep.*`)
  have hth := hs.threads
  have hclk := hs.clocks
  have hbef : ∀ c, L.Before m c → L.Before m' c := fun _ ⟨i, l, hl, hc⟩ =>
    ⟨i, l, hs.lockLoc (two_ap hW2) apE hl, hc⟩
  have hwd := fun W' (hW' : Two W') (h : W'.Ok m) =>
    hs.word_rmw h (two_word hW2 hW') (two_word (W := WE) (.inr rfl) hW')
  have hn' : CPh.Next ((G t).2.c) p := hn
  have hst0 : (C.prim L).Step t G (rsum (W.cellsR m) rY) m (upd G t (L.set (C.set (G t) p) q h))
      (rsum (W.cellsR m') rY) m' :=
    ⟨W, rY, hW, rfl, rfl, hY, hI, .inl ⟨p, q, h, ⟨hn, hq, hs, hEp, hsg⟩, hWI, rfl⟩⟩
  -- the new ghost values
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t (L.set (C.set (G t) p) q h) := ⟨_, rfl⟩
  rw [← hG'] at hI hsi hst0 ⊢
  have hG : ∀ u, u ≠ t → G' u = G u := fun u hu => by rw [hG']; exact upd_ne _ _ hu
  have hXt : (G' t).2 = { (G t).2 with c := p } := by rw [hG', upd_self]; rfl
  have hct : (G' t).2.c = p := by rw [hXt]
  have hLt : (G' t).1.ph = q := by rw [hG', upd_self]; rfl
  have hph : ∀ u, (G' u).2.ph = (G u).2.ph ∧ (G' u).2.sp = (G u).2.sp := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl⟩
  have hcu : ∀ u, u ≠ t → (G' u).2.c = (G u).2.c := fun u e => by rw [hG u e]
  -- the lock places: only a waiter's changes, between `out` and `away`
  have hheld : ∀ u, (L.ph (G u)).held = true → (L.ph (G' u)).held = true := fun u hu' => by
    by_cases e : u = t
    · subst e
      have hu'' : ((G u).1.ph).held = true := hu'
      show ((G' u).1.ph).held = true
      rw [hLt]
      rcases hq with ⟨rfl, -⟩ | ⟨h1, -⟩
      · exact hu''
      · rcases h1 with h1 | ⟨h1, -⟩ <;>
          (have h1' : (G u).1.ph = _ := h1; rw [h1'] at hu''; cases hu'')
    · rw [hG u e]; exact hu'
  have hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone := fun u hg => by
    by_cases e : u = t
    · subst e
      rcases hq with ⟨rfl, -⟩ | ⟨h1, -⟩
      · show (G u).1.ph ≠ .gone
        have : (G' u).1.ph ≠ .gone := hg
        rwa [hLt] at this
      · rcases h1 with h1 | ⟨h1, -⟩ <;> rw [h1] <;> decide
    · rwa [hG u e] at hg
  have hhb : ∀ c, L.HB G m c → L.HB G' m' c := fun _ hc =>
    hc.mono (fun u hu' => .inl (hheld u hu')) hclk hbef hth hgone
  -- the state's and the epoch's writes
  obtain ⟨hwS, hSh⟩ := hwd _ (.inl rfl) hu.um.ws
  obtain ⟨hwE, hEh⟩ := hwd _ (.inr rfl) hu.um.we
  have hSh' : WS.hist m' = WS.hist m ∨ ∃ x, WS.hist m' = (WS.hist m).push x :=
    hSh.imp_right fun ⟨_, _, _, e⟩ => ⟨_, e⟩
  -- the epoch moves only at a signaller's `inc → wk`
  have hEp' : WE.hist m' = WE.hist m ∨ ∃ q n h', (G t).2.c = .inc q n h' ∧ p = .wk n q h' := hEp
  -- two threads in the signal code are one (both hold the mutex)
  have hsig1 : ∀ u v, ((G u).2.c).sig = true → ((G v).2.c).sig = true → u = v := fun u v h1 h2 =>
    hWI.one u v (LPh.held_of_holds (sig_holds hu.cinv hu.sinv h1))
      (LPh.held_of_holds (sig_holds hu.cinv hu.sinv h2))
  -- no thread in the critical code while one is in the signal code
  have hcp : ∀ u v, ((G u).2.c).crit = true → ((G v).2.c).sig = true → False := fun u v h1 h2 =>
    hu.sinv.cp u v h1 (sig_pst hu.cinv h2)
  -- the epoch's writes: kept, or `t`'s `epoch += 1` at `inc → wk`
  have hEw : WE.hist m' = WE.hist m ∨ ((∃ q n h', (G t).2.c = .inc q n h') ∧
      (WE.hist m').size = (WE.hist m).size + 1 ∧ ∃ x : Word.Entry, x.clock = m'.clocks[t]! ∧
        WE.hist m' = (WE.hist m).push x) := by
    rcases hEp' with e | ⟨q₀, n₀, h₀, e, -⟩
    · exact .inl e
    · rcases hEh with e' | ⟨-, ord, v, e'⟩
      · exact .inl e'
      · exact .inr ⟨⟨q₀, n₀, h₀, e⟩, by rw [e', Array.size_push], _, rfl, e'⟩
  have hincE : ∀ q n h', (G t).2.c = .inc q n h' → ((G t).2.c).sig = true := fun _ _ _ e => by
    rw [e]; rfl
  -- registrations: no new one unless `t` registers from its load
  have hnr : (∀ u, ((G' u).2.c).isReg = true → ((G u).2.c).isReg = true) ∨
      (∃ i e, (G t).2.c = .ld i e) := by
    by_cases hr : ((G t).2.c).isReg = true
    · exact .inl fun u hr' => by
        by_cases e : u = t
        · subst e; exact hr
        · rwa [hcu u e] at hr'
    · by_cases hr' : p.isReg = true
      · obtain ⟨i, jr, sn, e, rfl⟩ := CPh.isReg_eq hr'
        cases hc : (G t).2.c with
        | ld i' e' => exact .inr ⟨i', e', rfl⟩
        | reg _ _ _ _ => rw [hc] at hr; exact absurd rfl hr
        | _ => rw [hc] at hn'; cases hn'
      · exact .inl fun u hr'' => by
          by_cases e : u = t
          · subst e; rw [hct] at hr''; exact absurd hr'' hr'
          · rwa [hcu u e] at hr''
  have hld : ∀ i e, p = .ld i e → (G t).2.c = .en → (WE.hist m).size = i + 1 ∧
      WE.hist m' = WE.hist m := fun i e hp hen => by
    obtain ⟨hi, hh⟩ := FCond.ld_newest (C := C) hu.lg.ehb (fun _ _ _ => rfl) (fun _ _ => rfl)
      hst0 hu.cinv hen (by show (G' t).2.c = _; rw [hct, hp])
    have hlt : i < (WE.hist m').size := (hI.ld t i e (by show (G' t).2.c = _; rw [hct, hp])).1
    have hh' : WE.hist m' = WE.hist m := hh
    have hi' : i = (WE.hist m).size - 1 := hi
    rw [hh'] at hlt
    exact ⟨by omega, hh'⟩
  -- the memory's part
  have hum : UM G' (rsum (W.cellsR m') rY) m' := by
    refine ⟨?_, fun e he hr => ?_, Rest.step (two_box hW2) hu.um.rest rfl hY
        fun l _ hw => hs.cells hw,
      hu.um.blk.of_block fun _ _ hb => hs.block hb, hwS, hwE, fun w hw => ?_⟩
    · exact hu.um.shape.congr hth (funext fun u => (hph u).1)
    · rcases (hs.fp he).imp_right fun h => h.elim (two_fp hW2) (two_fp (.inr rfl)) with
        h' | ⟨-, ho⟩
      · rcases hu.um.io e h' hr with ⟨hk, h''⟩ | h''
        · exact .inl ⟨hk, Conc.someLe_mono hth (fun u _ => hclk u) h''⟩
        · exact .inr (Conc.allLe_mono hth (fun u _ => hclk u) h'')
      · have := hr.2.2; omega
    · rcases hs.waiters hw with h' | rfl
      · exact hu.um.q w h'
      · exact .inr rfl
  refine ⟨hum, hI, hsi, ⟨by rw [(hph 0).1, (hph 1).1]; exact hu.lg.one, fun u k s h' => ?_,
    fun u h' => by rw [(hph u).2] at h'; rw [(hph u).1]; exact hu.lg.wtx u h',
    hu.lg.ehb.step hhb ?_, fun u i e h' => ?_, fun u v hr hc => ?_, fun u i jr sn e h' => ?_,
    fun u i jr sn e v q' n h' hu' hv => ?_, fun u i jr sn e h' hsz => ?_,
    fun v q' n h' hv => ?_⟩⟩
  · -- tot
    rw [(hph u).1] at h'
    rw [show xs G' = xs G from funext fun u => (hph u).1]; exact hu.lg.tot u k s h'
  · -- ehb: the new epoch write is the holder's
    rcases hEw with e | ⟨⟨q₀, n₀, h₀, e⟩, -, x, hx, e'⟩
    · exact .inl e
    · refine .inr ⟨x, e', FLock.HB.of_holder (t := t) (hheld t (LPh.held_of_holds ?_))
      (by rw [hx]; exact VClock.le_refl _)⟩
      exact sig_holds hu.cinv hu.sinv (by rw [e]; rfl)
  · -- f0
    by_cases et : u = t
    · subst et
      rw [hct] at h'
      subst h'
      cases hc : (G u).2.c with
      | en => rw [(hld i e rfl hc).2]; exact (hld i e rfl hc).1
      | ld i₀ e₀ =>
        rw [hc] at hn'
        have hn2 : CPh.ld i₀ e₀ = CPh.ld i e := hn'
        cases hn2
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e']; exact hu.lg.f0 u _ _ hc
        · rw [hc] at e'; cases e'
      | _ => have hcr := hn'.crit rfl; rw [hc] at hcr; cases hcr
    · rw [hcu u et] at h'
      rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
      · rw [e']; exact hu.lg.f0 u i e h'
      · exact (hcp u t (by rw [h']; rfl) (hincE _ _ _ e')).elim
  · -- rc
    by_cases eu : u = t
    · subst eu
      by_cases ev : v = u
      · subst ev; rw [hct] at hr hc
        obtain ⟨_, _, _, _, rfl⟩ := CPh.isReg_eq hr; cases hc
      · rw [hcu v ev] at hc; rw [hct] at hr
        cases hr0 : ((G u).2.c).isReg
        · exact ev (hu.cinv.crit1 v u hc (hn'.crit_of_reg hr (by simpa using hr0)))
        · exact hu.lg.rc u v hr0 hc
    · rw [hcu u eu] at hr
      by_cases ev : v = t
      · subst ev; rw [hct] at hc; exact hu.lg.rc u v hr (hn'.crit hc)
      · rw [hcu v ev] at hc; exact hu.lg.rc u v hr hc
  · -- f2
    by_cases et : u = t
    · subst et
      rw [hct] at h'
      rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
      · rw [e']
        rw [h'] at hn'
        cases hc : (G u).2.c with
        | ld i₀ e₀ =>
          rw [hc] at hn'; obtain ⟨rfl, -, -⟩ := hn'
          have := hu.lg.f0 u _ _ hc; omega
        | reg i₀ jr₀ sn₀ e₀ =>
          rw [hc] at hn'; obtain ⟨-, hi⟩ := hn'
          have := hu.lg.f2 u i₀ jr₀ sn₀ e₀ hc; omega
        | _ => rw [hc] at hn'; cases hn'
      · rw [e'] at hn'; rw [h'] at hn'; cases hn'
    · rw [hcu u et] at h'
      rcases hEw with e' | ⟨⟨q₀, n₀, h₀, e'⟩, hsz, -⟩
      · rw [e']; exact hu.lg.f2 u i jr sn e h'
      · have := hu.lg.f3 u i jr sn e t q₀ n₀ h₀ h' e'; omega
  · -- f3
    by_cases et : u = t
    · subst et
      rw [hct] at hu'
      have hvt : v ≠ u := fun e => by subst e; rw [hct] at hv; rw [hu'] at hv; cases hv
      rw [hcu v hvt] at hv
      rw [hu'] at hn'
      cases hc : (G u).2.c with
      | ld i₀ e₀ => exact (hcp u v (by rw [hc]; rfl) (by rw [hv]; rfl)).elim
      | reg i₀ jr₀ sn₀ e₀ =>
        rw [hc] at hn'; obtain ⟨-, hi⟩ := hn'
        have := hu.lg.f3 u i₀ jr₀ sn₀ e₀ v q' n h' hc hv
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e']; omega
        · rw [hc] at e'; cases e'
      | _ => rw [hc] at hn'; cases hn'
    · rw [hcu u et] at hu'
      by_cases ev : v = t
      · subst ev
        rw [hct] at hv
        rw [hv] at hn'
        rcases hn'.to_inc with ⟨sh, c, hc⟩ | hc
        · -- `t`'s post: the epoch has at most one write after `u`'s saved one, else the state
          -- write before it is sated (`f4`), and no post follows a sated write
          have hpf := post_facts hu.cinv (g' := L.set (C.set (G v) p) q h)
            (by rw [← hG']; exact hI) hc (by show p = _; exact hv)
            (by rw [← hG']; show C.SigStep v (C.ph (G v)) (G' v).2.c m m'; rw [hct]; exact hsg)
          have hE : WE.hist m' = WE.hist m := by
            rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
            · exact e'
            · rw [hc] at e'; cases e'
          rw [hE]
          have h2 := hu.lg.f2 u i jr sn e hu'
          refine Classical.byContradiction fun hne => hpf.1 (hu.lg.f4 u i jr sn e hu' (by omega))
        · have := hu.lg.f3 u i jr sn e v q' n h' hu' hc
          rcases hEp' with e' | ⟨_, _, _, -, ep⟩
          · rw [e']; exact this
          · rw [hv] at ep; cases ep
      · rw [hcu v ev] at hv
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e']; exact hu.lg.f3 u i jr sn e v q' n h' hu' hv
        · exact absurd (hsig1 v t (by rw [hv]; rfl) (hincE _ _ _ e')) ev
  · -- f4
    by_cases et : u = t
    · subst et
      rw [hct] at h'
      rw [h'] at hn'
      cases hc : (G u).2.c with
      | ld i₀ e₀ =>
        rw [hc] at hn'; obtain ⟨rfl, -, -⟩ := hn'
        have := hu.lg.f0 u _ _ hc
        rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
        · rw [e'] at hsz; omega
        · rw [hc] at e'; cases e'
      | reg i₀ jr₀ sn₀ e₀ =>
        rw [hc] at hn'; obtain ⟨-, hi⟩ := hn'
        have hE : WE.hist m' = WE.hist m := by
          rcases hEw with e' | ⟨⟨_, _, _, e'⟩, -⟩
          · exact e'
          · rw [hc] at e'; cases e'
        rw [hE] at hsz
        have h2 := hu.lg.f2 u i₀ jr₀ sn₀ e₀ hc
        refine sated_keep hu.cinv hI ?_ hSh' (hu.lg.f4 u i₀ jr₀ sn₀ e₀ hc (by omega))
        rcases hnr with hnr | ⟨_, _, e'⟩
        · exact hnr
        · rw [hc] at e'; cases e'
      | _ => rw [hc] at hn'; cases hn'
    · rw [hcu u et] at h'
      -- no registration of `t` while `u` is registered (`rc`)
      have hnr' : ∀ u, ((G' u).2.c).isReg = true → ((G u).2.c).isReg = true := by
        rcases hnr with hnr | ⟨_, _, e'⟩
        · exact hnr
        · exact (hu.lg.rc u t (by rw [h']; rfl) (by rw [e']; rfl)).elim
      rcases hEw with e' | ⟨⟨q₀, n₀, h₀, e'⟩, hsz', -⟩
      · rw [e'] at hsz; exact sated_keep hu.cinv hI hnr' hSh' (hu.lg.f4 u i jr sn e h' hsz)
      · exact sated_keep hu.cinv hI hnr' hSh' (hu.lg.incS t q₀ n₀ h₀ e')
  · -- incS
    by_cases ev : v = t
    · subst ev
      rw [hct] at hv
      rw [hv] at hn'
      rcases hn'.to_inc with ⟨sh, c, hc⟩ | hc
      · -- `t`'s post, with at most one waiter (the other thread)
        have hpf := post_facts hu.cinv (g' := L.set (C.set (G v) p) q h)
          (by rw [← hG']; exact hI) hc (by show p = _; exact hv)
          (by rw [← hG']; show C.SigStep v (C.ph (G v)) (G' v).2.c m m'; rw [hct]; exact hsg)
        refine hpf.2.1 (wle1 hI (1 - v) fun u hr => ?_)
        have hv2 : v < 2 := lt2 hu.um hu.sinv (by
          have := sig_pst hu.cinv (u := v) (by rw [hc]; rfl)
          intro e; rw [e] at this; cases this)
        have huv : u ≠ v := fun e => by subst e; rw [hct, hv] at hr; cases hr
        have hw : ((G' u).2.c).waits = true := CPh.isReg_waits hr
        have hu2 : u < 2 := lt2 hum hsi fun e => by
          have h1 : (G' u).2.sp = .wt := hsi.wt u hw
          rw [e] at h1; cases h1
        unfold ThreadId at *; omega
      · have hnr' : ∀ u, ((G' u).2.c).isReg = true → ((G u).2.c).isReg = true := by
          rcases hnr with hnr | ⟨_, _, e'⟩
          · exact hnr
          · rw [hc] at e'; cases e'
        exact sated_keep hu.cinv hI hnr' hSh' (hu.lg.incS v q' n h' hc)
    · rw [hcu v ev] at hv
      have hnr' : ∀ u, ((G' u).2.c).isReg = true → ((G u).2.c).isReg = true := by
        rcases hnr with hnr | ⟨_, _, e'⟩
        · exact hnr
        · exact (hcp t v (by rw [e']; rfl) (by rw [hv]; rfl)).elim
      exact sated_keep hu.cinv hI hnr' hSh' (hu.lg.incS v q' n h' hv)

/-! ## The protocol has the semaphore -/

/-- **A step of the semaphore's primitive or a tick keeps `U`** (`FLock.Fits.kstep`). -/
theorem kstep (t : ThreadId) (G : ThreadId → Gh) (rX : Res) (m : Mem) (G' : ThreadId → Gh)
    (rX' : Res) (m' : Mem) (hs : S.prim.Step t G rX m G' rX' m' ∨ L.PartTick t G rX m G' rX' m')
    (hu : U G rX m) : U G' rX' m' := by
  rcases hs with ⟨hsi, hs | ⟨hci, hs⟩⟩ | hs
  · rcases hs with ⟨W, rY, hW, rfl, rfl, hY, hI,
      ⟨p, q, h, ⟨hn, hq, hs, hEp, hsg⟩, hWI, rfl⟩ | ⟨r, -, hi, -, hs, -, hw', hh, hL, rfl⟩⟩
    · exact cstep G rY m m' t p q h W hW hn hq hu hY hs hEp hsg hWI hI hsi
    · exact U_own hW hu hi hY hs hw' hh hL rfl rfl hI hsi
  · cases hs with
    | enter _ hct hst hwx hcnt => exact U_enter hu hct hst hwx hcnt hci hsi
    | hold s h hlt _ hL _ hfs hL' _ hgo => exact U_hold hu hL hfs hL' hgo hlt hci hsi
  · exact tickStable t G rX m G' rX' m' hs hu

/-- `R` reads the threads' places in the program only. -/
theorem R_congr {Y Y' : ThreadId → X} (h : ∀ u, (Y' u).ph = (Y u).ph) : R Y' = R Y := by
  have : (fun u => (Y' u).ph) = fun u => (Y u).ph := funext h
  unfold R; rw [this]

variable {Tgt : Type} {semOf : Tgt → Option Ptr}

/-- **The protocol has the semaphore** (`FSem.Fits`); the window: at most one epoch write after a
registered waiter's saved one (`f2`). -/
theorem fits : S.Fits (proto semOf) U ok where
  ok_s _ h := h.2
  win _ _ m hu u i jr e hc _ _ := by
    have : (C.Ep.hist m).size ≤ i + 2 := hu.lg.f2 u i jr false e hc
    omega
  toFits := {
    inv := fun _ _ => Iff.rfl
    fin := fun _ h => h.1
    joins := fun _ h => h.1
    ok_set := fun _ _ _ => Iff.rfl
    ok_setPart := fun _ _ => Iff.rfl
    stable := stable
    atStop := fun _ _ _ t _ hu => atStop t hu
    kfin := fun g h => by show (g.2.c, g.2.sp) = (CPh.out, SPh.out); rw [h.2]
    kjoins := fun g h => by show (g.2.c, g.2.sp) = (CPh.out, SPh.out); rw [h.2]
    sub := fun _ _ _ hu => ⟨⟨hu.cinv, fun W hW => by
      rcases hW with rfl | rfl
      · exact ⟨hu.um.ws, Rest.split (fun _ => ws_box) hu.um.rest⟩
      · exact ⟨hu.um.we, Rest.split (fun _ => we_box) hu.um.rest⟩⟩, hu.sinv⟩
    apart := fun W hW => by rcases hW with rfl | rfl <;> first | exact apS | exact apE
    lph := fun _ _ => rfl
    lpart := fun _ _ => rfl
    lheld := fun _ _ => rfl
    lR := fun G t p r hr => by
      change R (fun u => (upd G t (S.place.set (G t) p) u).2) r
      rw [R_congr (Y := fun u => (G u).2) fun u => by
        by_cases e : u = t
        · subst e; rw [upd_self]; rfl
        · rw [upd_ne _ _ e]]
      exact hr
    ph_l := fun _ _ _ => rfl
    set_l := fun _ _ _ _ => rfl
    ph_part := fun _ _ => rfl
    set_part := fun _ _ _ => rfl
    role_l := fun _ _ _ _ => Iff.rfl
    role_part := fun _ _ _ => Iff.rfl
    ok_calm := fun _ _ _ hp hq => ⟨fun _ => hq, fun _ => hp⟩
    kstep := kstep
    holdLive := fun _ _ _ _ hi _ hv => FLock.holdLive_none (fun _ h => h) hi hv }

end SemCounter
end Zig
