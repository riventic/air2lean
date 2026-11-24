import ZigLean.Sep.Full.RwLockProd
import ZigLean.Sep.Full.CondWindow
import ZigLean.Sep.Full.LockRest

/-!
# The reader/writer lock's base in the two-lock product

(ledger #two-lock-product, item (5).) `FRw.fitsM`, `FRw.fitsS` and `FRw.Fits.ofProduct`
(`ZigLean/Sep/Full/RwLockProd.lean`) build the reader/writer protocol from a client's base `U₀` at
the common rest of the two-lock product. `FRw.Base` is that base for a client with no rest of its
own beside the lock's: what every client's base keeps, for every reader/writer lock `W`.

- `winv`: the rwlock's invariant (`fitsM`'s `hsub`).
- `sub`: the semaphore's primitive's rest, the condition's and the semaphore's invariants and the
  condition's words (`fitsS`'s `hsub`).
- `win`: the condition's window with one registered waiter (`FCond.Win1`; `fitsS`'s `win`).
- `shares`: the readers' shares (`FRw.Shares`), which give `Inv.stepIn`'s `hrd`.
- `pin`: the extent of the lock's block (`Res.Pins`), which gives `Inv.stepIn`'s `hcells`
  (`FLock.Inv.cells_pinned`).
- `wt`, `nap`: the places at the semaphore and at the outer mutex go together: only the writer at
  `ww` waits at the semaphore (`Fits.ofProduct`'s `wtw`), and a thread in the semaphore's mutex's
  code or in the semaphore's is `away` from the outer mutex or holds it at `holdsAway` (`fitsS`'s
  `hsleep`: `Base.hsleep`).
- `live`: the rest's owned bytes are live (`Inv.stepIn`'s `hbl`).

The obligations of the builders, one theorem each: a stop (`Base.atStop`), a step of either
lock's code (`Base.stableM`, `Base.stableS`), a tick of a thread's part in the outer mutex's view
and in the semaphore's (`Base.tickM`, `Base.tickL`, from `Base.tick`), a step of the rwlock's own
code (`Base.wstep`), a step of the semaphore's code (`Base.sstep`: `fitsS`'s `kstep`, from the
assembler `Base.ofStepRest` over the rest the step leaves, `FCond.StepRest`, and `Base.natStep` for
a step in the semaphore's mutex's frame), and the relabels around the other lock's code
(`Base.mnap`, `Base.munnap`, `Base.maway`, `Base.munaway`, `Base.lmove`, from `Base.relabel`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

variable (W) in
/-- **The base of a client of the reader/writer lock** at the common rest `rX` of the two-lock
product (module doc); the lock's block has `Sz` bytes of kind `K`. -/
structure Base (Sz : Nat) (K : BlockKind) (G : ThreadId → γ) (rX : Res) (m : Mem) : Prop where
  winv : W.Inv G rX m
  sub : S.prim.Sub G rX m
  win : C.Win1 L G m
  shares : W.Shares G m
  pin : rX.Pins W.st.b Sz K
  /-- Only the writer at `ww` waits at the semaphore (`Fits.ofProduct`'s `wtw`). -/
  wt : ∀ u, S.ph (G u) = .wt → W.ph (G u) = .ww
  /-- A thread in the semaphore's mutex's code (not `out`, `away` or ended) or in the semaphore's
  is `away` from the outer mutex or holds it at `holdsAway` (`fitsS`'s `hsleep`). -/
  nap : ∀ u, (L.ph (G u) ≠ .out ∧ L.ph (G u) ≠ .away ∧ L.ph (G u) ≠ .gone) ∨
      S.place.ph (G u) ≠ (.out, .out) →
    M.ph (G u) = .away ∨ M.ph (G u) = .holdsAway
  /-- The rest's bytes are live (`Inv.stepIn`'s `hbl`; a step of the condition's code carries
  no lock invariant to read it from, `FPrim.ofWords`). -/
  live : ∀ l, rX.owned l ≠ none → m.heap l ≠ none

namespace Base

variable {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {rX : Res} {m : Mem}

/-- **A thread out of the semaphore's mutex's code that is no writer at `ww` is out of the
semaphore's and the condition's code**: only the writer at `ww` is at `wt` (`wt`), a thread at
`pst` holds the mutex (`FSem.Inv.pst`), and out of the semaphore's code it is out of the
condition's (`FSem.Inv.c_out`). -/
theorem sout {u : ThreadId} (hu : W.Base Sz K G rX m) (hl : L.ph (G u) = .out)
    (hw : W.ph (G u) ≠ .ww) : S.place.ph (G u) = (.out, .out) := by
  obtain ⟨⟨hC, -⟩, hS⟩ := hu.sub
  have hs : S.ph (G u) = .out := by
    cases e : S.ph (G u) with
    | out => rfl
    | wt => exact absurd (hu.wt u e) hw
    | pst h c =>
      have := hS.pst u (by rw [e]; rfl)
      rw [hl] at this; cases this
  exact Prod.ext (hS.c_out hC hs) hs

/-- A thread out of the outer mutex's code, or holding it awake, is out of the semaphore's and the
condition's code (`nap`). -/
theorem sout_of_m {u : ThreadId} (hu : W.Base Sz K G rX m)
    (hm : M.ph (G u) = .out ∨ M.ph (G u) = .holds) : S.place.ph (G u) = (.out, .out) :=
  Classical.byContradiction fun h => by
    rcases hu.nap u (.inr h) with e | e <;> rcases hm with e' | e' <;> rw [e] at e' <;> cases e'

/-- **A stop keeps the base** (`fitsM`'s and `fitsS`'s `atStop`): no part of it reads the current
thread. -/
theorem atStop (hu : W.Base Sz K G rX m) (t : ThreadId) :
    W.Base Sz K G rX { m with current := t } := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m.clocks[u]!) = true :=
    fun _ => VClock.le_refl _
  exact {
    winv := hu.winv.queue t m.waiters m.woken
    sub := ⟨⟨hC.stay (m' := { m with current := t }) rfl rfl rfl rfl rfl (fun _ hw _ => hw)
        (fun _ _ h => h) (Nat.le_refl _) hcl,
      fun Wd hWd => by
        obtain ⟨hok, rY, e, hY⟩ := hW Wd hWd
        exact ⟨(hok.fields_native (m' := { m with current := t }) rfl rfl rfl rfl hcl).1, rY, e,
          hY⟩⟩,
      hS.mono (m' := { m with current := t }) (fun _ => rfl) (fun _ => rfl) rfl hS.pst
        (fun _ h => .inl h) hcl (fun _ h => h) rfl (fun _ h => h) (fun _ h => .inl h) rfl rfl⟩
    win := hu.win.keep (fun _ => rfl) rfl rfl hu.win.ehb
    shares := hu.shares
    pin := hu.pin
    wt := hu.wt
    nap := hu.nap
    live := hu.live }

/-- **A step of the outer mutex's code keeps the base** (`fitsM`'s `stable`): `t` runs it at a
calm place of the rwlock, out of the semaphore's code. The rwlock's invariant stays
(`Inv.otherStep`: `t` holds no writing bit at a calm place), the semaphore's primitive's rest
stays (`FSem.Sub.otherLock`), the window stays (the condition's writes stay, and every epoch write
still happened before the semaphore's mutex's holder), and the parts stay (`FLock.part_set`). The
outer mutex's place is none of the rwlock's or the semaphore's (`hpm`). -/
theorem stableM {t : ThreadId} {p : LPh} {h rL rH : Res} {m' : Mem} (hu : W.Base Sz K G rX m)
    (hM : M.Inv G (rsum (FLock.side L m rL rH) rX) m) (hk : L.Keeps G m rL rH rX)
    (hs : M.Step t m m') (hn : (M.ph (G t)).next p = true) (hla : L.ph (G t) = .away)
    (hcalm : W.prim.calm (W.place.ph (G t)))
    (hpm : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g) :
    W.Base Sz K (upd G t (M.set (G t) p h)) rX m' := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have hup : ∀ {α : Type} (f : γ → α), (∀ g, f (M.set g p h) = f g) →
      ∀ u, f (upd G t (M.set (G t) p h) u) = f (G u) := fun f hf u => by
    have := congrFun (upd_map f G t (hf (G t))) u
    rwa [upd_same] at this
  have hwph := hup W.ph fun g => congrArg Prod.fst (hpm g p h)
  have hcph := hup C.ph fun g => congrArg (fun q => q.2.1) (hpm g p h)
  have hlph := hup L.ph fun g => W.pair.ph_ab g p h
  have hapL : L.ApartL M.toLockWord := W.pair.apart.symm
  have hS' := ((hW C.S (.inl rfl)).1.lockStep hs (c_apart W _ (.inl rfl)).2).2
  have hE' := ((hW C.Ep (.inr rfl)).1.lockStep hs (c_apart W _ (.inr rfl)).2).2
  have hnw : (W.ph (G t)).isW = false := by
    have hc : W.ph (G t) = .out ∨ W.ph (G t) = .wi ∨ (W.ph (G t)).isRd = true := hcalm.1
    cases e' : W.ph (G t) <;> rw [e'] at hc <;> first | rfl | simp [RwPh.isRd] at hc
  have hpv : S.cnt (upd G t (M.set (G t) p h)) = S.cnt G := cnt_congr hwph
  exact {
    winv := Inv.otherStep hM hu.winv hs (st_apart W).2 hwph (hup W.x fun g => W.x_m g p h)
      (fun u hg => by
        by_cases e : u = t
        · rw [e]; exact LPh.ne_gone_of_next hn
        · rwa [upd_ne _ _ e] at hg)
      (fun u hw => by
        by_cases e : u = t
        · rw [e, hnw] at hw; cases hw
        · rw [upd_ne _ _ e]; exact hu.winv.wm u hw)
    sub := FSem.Sub.otherLock hu.sub (fun Wd hWd => (c_apart W Wd hWd).2) hapL hk.facts.w.blk
      (ep_key_ne W m) hcalm.2 ((congrArg Prod.snd (hpm (G t) p h)).trans hcalm.2)
      (W.pair.ph_ab _ _ _) hpv hs
    win := hu.win.keep hcph hS' hE' (hu.win.ehb.step
      (fun _ hc => hc.mono (fun u hh => .inl (by rw [hlph u]; exact hh)) hs.clocks
        (fun _ hb => LockWord.Before.otherStep hs hapL hb) hs.threads
        fun u hg => by rwa [hlph u] at hg)
      (.inl hE'))
    shares := hu.shares.congr hwph
      (fun v hv => by rwa [LockWord.joinedB_congr hs.threads] at hv)
      fun v l => by rw [hup M.part fun g => M.part_set g p h]
    pin := hu.pin
    wt := fun u hq => by
      rw [hwph u]
      exact hu.wt u (by rwa [hup S.ph (fun g => congrArg (fun q => q.2.2) (hpm g p h)) u] at hq)
    nap := fun u hq => by
      rw [hlph u, hup S.place.ph (fun g => congrArg Prod.snd (hpm g p h)) u] at hq
      by_cases e : u = t
      · rw [e] at hq
        rcases hq with ⟨-, hq, -⟩ | hq
        · exact absurd hla hq
        · exact absurd hcalm.2 hq
      · rw [upd_ne _ _ e]; exact hu.nap u hq
    live := fun l hl => by
      rw [hs.heap (hM.notIn_side l hl)]; exact hu.live l hl }

/-- **A step of the semaphore's mutex's code keeps the base** (`fitsS`'s `stable`): `t` runs it
out of the condition's busy code and out of the semaphore's `pst` (the client's `okS`: `hb`,
`hst`). The rwlock's invariant stays (`Inv.otherStep`), the condition's and the semaphore's by
their own lock steps (`FCond.Inv.lstep`, `FSem.Inv.lstep`; the condition's words are apart from
the mutex's, `c_apart`, `FSem.ep_key_ne`), the window by `FLock.WordHB.lstep`, and the parts
stay. The mutex's place is none of the semaphore's (`hpl`). -/
theorem stableS {t : ThreadId} {p : LPh} {h s : Res} {m' : Mem} (hu : W.Base Sz K G rX m)
    (hL : L.Inv G (rsum s rX) m) (hs : L.Step t m m') (hn : (L.ph (G t)).next p = true)
    (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!))
    (hb : (C.ph (G t)).busy = false) (hst : S.ph (G t) = .out ∨ S.ph (G t) = .wt)
    (hma : M.ph (G t) = .away ∨ M.ph (G t) = .holdsAway)
    (hpl : ∀ g q h, S.place.ph (L.set g q h) = S.place.ph g) :
    W.Base Sz K (upd G t (L.set (G t) p h)) rX m' := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have hg := LPh.ne_gone_of_next hn
  have hz := LPh.ne_holdsAway_of_next hn
  have cph : ∀ g q h, C.ph (L.set g q h) = C.ph g := fun g q h => congrArg Prod.fst (hpl g q h)
  have sph : ∀ g q h, S.ph (L.set g q h) = S.ph g := fun g q h => congrArg Prod.snd (hpl g q h)
  have hup : ∀ {α : Type} (f : γ → α), (∀ g, f (L.set g p h) = f g) →
      ∀ u, f (upd G t (L.set (G t) p h) u) = f (G u) := fun f hf u => by
    have := congrFun (upd_map f G t (hf (G t))) u
    rwa [upd_same] at this
  have hwph := hup W.ph fun g => W.ph_l g p h
  have hmph := hup M.ph fun g => W.pair.ph_ba g p h
  have hap := c_apart W
  have hwS := (hW C.S (.inl rfl)).1
  have hwE := (hW C.Ep (.inr rfl)).1
  have hstp : (S.ph (G t)).isPst = false := by rcases hst with e | e <;> rw [e] <;> rfl
  exact {
    winv := Inv.otherStep hL hu.winv hs (st_apart W).1 hwph (hup W.x fun g => W.x_l g p h)
      (fun u hg => by rwa [hmph u] at hg) (fun u hw => by rw [hmph u]; exact hu.winv.wm u hw)
    sub := ⟨⟨hC.lstep hwS hwE (hap _ (.inl rfl)).1 (hap _ (.inr rfl)).1 (S.ep_key_ne m) hb
        (LPh.ne_away_of_next hn) cph hs,
      fun Wd hWd => by
        obtain ⟨hok, rY, e, hY⟩ := hW Wd hWd
        have hcl : Wd.cellsR m' = Wd.cellsR m :=
          cellsAt_congr fun l hl => hs.heap ((hap Wd hWd).1.not_in hl)
        exact ⟨(hok.lockStep hs (hap Wd hWd).1).1, rY, by rw [hcl]; exact e, hY⟩⟩,
      hS.lstep hwS (hap _ (.inl rfl)).1 cph sph hstp hg hz hs hrel⟩
    win := hu.win.keep (hup C.ph fun g => cph g p h) (hwS.lockStep hs (hap _ (.inl rfl)).1).2
      (hwE.lockStep hs (hap _ (.inr rfl)).1).2
      (hu.win.ehb.lstep hwE (hap _ (.inr rfl)).1 hg hz hs hrel)
    shares := hu.shares.congr hwph
      (fun v hv => by rwa [LockWord.joinedB_congr hs.threads] at hv)
      fun v l => by
        rw [hup M.part fun g => by rw [W.pair.part, L.part_set, ← W.pair.part]]
    pin := hu.pin
    wt := fun u hq => by
      rw [hwph u]; exact hu.wt u (by rwa [hup S.ph (fun g => sph g p h) u] at hq)
    nap := fun u hq => by
      rw [hmph u]
      by_cases e : u = t
      · rw [e]; exact hma
      · rw [upd_ne _ _ e] at hq; exact hu.nap u hq
    live := fun l hl => by
      rw [hs.heap (hL.notIn_side l hl)]; exact hu.live l hl }

/-- **A tick of `t`'s part keeps the base** (the two locks have one part,
`FLock.Pair.setPart`): the tick changes no byte, so the rwlock's invariant stays (`Inv.stepIn`;
the rest's bytes are live, `FLock.Inv.rest_live`), the condition's and the semaphore's stay
(`FCond.Inv.other`, `FSem.Inv.outStep`), and the readers' shares are kept by counting
(`Shares.keep`), given the outer mutex's invariant before and after the tick at rests with the
common rest beside the semaphore's mutex's side (`s`, `s'`: the same shares). The part is no
place (`hpl`). -/
theorem tick {t : ThreadId} {r s s' : Res} (hu : W.Base Sz K G rX m)
    (hM : M.Inv G (rsum s rX) m)
    (hM' : M.Inv (upd G t (M.setPart (G t) r)) (rsum s' rX) m.ticked)
    (hs : ∀ l, s'.gh.share l = s.gh.share l) (ht : t < m.threads.size)
    (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g) :
    W.Base Sz K (upd G t (M.setPart (G t) r)) rX m.ticked := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have wph : ∀ g, W.ph (M.setPart g r) = W.ph g := fun g => congrArg Prod.fst (hpl g r)
  have cph : ∀ g, C.ph (M.setPart g r) = C.ph g := fun g =>
    congrArg (fun q => q.2.1) (hpl g r)
  have sph : ∀ g, S.ph (M.setPart g r) = S.ph g := fun g =>
    congrArg (fun q => q.2.2) (hpl g r)
  have lph : ∀ g, L.ph (M.setPart g r) = L.ph g := fun g => by
    rw [W.pair.setPart, L.ph_setPart]
  have hup : ∀ {α : Type} (f : γ → α), (∀ g, f (M.setPart g r) = f g) →
      ∀ u, f (upd G t (M.setPart (G t) r) u) = f (G u) := fun f h u => by
    have := congrFun (upd_map f G t (h (G t))) u
    rwa [upd_same] at this
  have hwph := hup W.ph wph
  have hmph := hup M.ph fun g => M.ph_setPart g r
  have hlph := hup L.ph lph
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m.ticked.clocks[u]!) = true :=
    fun _ => VClock.le_refl _
  have hfld : ∀ {Wd : Word 32 4} {A : ThreadId → Prop}, Wd.Ok m A →
      Wd.Ok m.ticked A ∧ Wd.hist m.ticked = Wd.hist m :=
    fun h => h.fields_native rfl rfl rfl rfl hcl
  have hS' := (hfld (hW C.S (.inl rfl)).1).2
  have hE' := (hfld (hW C.Ep (.inr rfl)).1).2
  have hpv : S.cnt (upd G t (M.setPart (G t) r)) = S.cnt G := cnt_congr hwph
  exact {
    winv := hu.winv.stepIn (FStepIn.ticked m rX.owned) (fun _ h => h)
      (fun l h => hM.rest_live ((Res.owned_sep rfl rfl).mpr (.inr h))) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ _ _ h => absurd rfl h) hwph (hup W.x fun g => W.x_part g r)
      (fun u h => by rwa [hmph u] at h) (fun u h => by rw [hmph u]; exact hu.winv.wm u h)
    sub := ⟨⟨hC.other (t := t) (g' := M.setPart (G t) r) (cph _) (fun _ => lph _)
        (fun _ h => by rw [lph]; exact h)
        (by rw [S.sx_iff, S.sx_iff, sph]; exact id) hS' hE' rfl rfl rfl
        (fun w hw _ => .inl hw) (fun _ _ _ h => h) (Nat.le_refl _) hcl,
      fun Wd hWd => by
        obtain ⟨hok, rY, e, hY⟩ := hW Wd hWd
        exact ⟨(hfld hok).1, rY, e, hY⟩⟩,
      hS.outStep (t := t) (g' := M.setPart (G t) r) (sph _) (cph _) (lph _) hpv hcl
        (fun _ h => h) rfl (fun w hw hn => absurd hw hn) rfl hS'⟩
    win := hu.win.keep (hup C.ph cph) hS' hE' (hu.win.ehb.step
      (fun _ hc => hc.mono (fun u h => .inl (by rw [hlph u]; exact h)) hcl (fun _ h => h) rfl
        fun u h => by rwa [hlph u] at h)
      (.inl hE'))
    shares := hu.shares.keep hM hM'
      (fun l => by
        show (s'.gh.share l).add (rX.gh.share l) = (s.gh.share l).add (rX.gh.share l)
        rw [hs l])
      (fun u q H l c hq hl => SCell.pos_add' _ (hu.winv.rest_share hq hl)) rfl
      ht (fun u e => upd_ne _ _ e) (by rw [upd_self, wph])
    pin := hu.pin
    wt := fun u hq => by rw [hwph u]; exact hu.wt u (by rwa [hup S.ph sph u] at hq)
    nap := fun u hq => by
      rw [hmph u]
      rw [hlph u, hup S.place.ph (fun g => congrArg Prod.snd (hpl g r)) u] at hq
      exact hu.nap u hq
    live := hu.live }

/-- **A waiter of the condition is `away` from the outer mutex or holds it at `holdsAway`**
(`fitsS`'s `hsleep`; `nap`), with the epoch in the outer mutex's nest (`hnE`, the lock's). -/
theorem hsleep (hnE : M.nest C.Ep.ptr) {t : ThreadId} (hu : W.Base Sz K G rX m)
    (hw : (C.ph (G t)).waits = true) :
    M.ph (G t) = .away ∨ (M.ph (G t) = .holdsAway ∧ M.nest C.Ep.ptr) :=
  (hu.nap t (.inr fun e => by
    have hc : C.ph (G t) = .out := congrArg Prod.fst e
    rw [hc] at hw; cases hw)).imp id fun h => ⟨h, hnE⟩

/-- **A step of the rwlock's own code keeps the base** (`fitsM`'s `kstep`), but for the readers'
shares after it (`hsh`; ledger #two-lock-product, the ninth obstruction: `Step` does not fix the
stepping thread's new place). The rwlock's invariant after the step is `fitsM`'s; the semaphore's
primitive's rest stays (`semSub_step`); the condition's writes stay in the step's frame
(`Step.frame`), so the window stays; the free resource claims no extent (`FreeRes.extent`), so
the pin stays in the rest of the rest; and the stepping thread is out of the semaphore's code,
with its places at both mutexes kept. -/
theorem wstep {t : ThreadId} {G' : ThreadId → γ} {rS rS' sB rX' rY rY' : Res} {m' : Mem}
    {P : ThreadId → LPh} (hu : W.Base Sz K G rX m) (hs : W.Step t G rS m G' rS' m')
    (hS' : rS' = rsum sB rX') (hLw : L.WInv P m) (hI' : W.Inv G' rX' m')
    (he : rX = rsum (W.st.cellsR m) rY) (he' : rX' = rsum (W.st.cellsR m') rY')
    (hmv : W.Moves G m rY G' m' rY')
    (hRoff : ∀ xs r l, W.R xs r → (C.S.In l ∨ C.Ep.In l) → r.heap l = none)
    (hsh : W.Shares G' m') : W.Base Sz K G' rX' m' := by
  obtain ⟨⟨-, hW⟩, -⟩ := hu.sub
  have hsub' := semSub_step hs hu.sub hLw hRoff he he' hmv
  have hM' : M.Inv G' (rsum sB rX') m' := hS' ▸ hs.2.2.1
  obtain ⟨hF, hfs, hFm⟩ := hs.frame
  obtain ⟨-, -, -, -, -, -, hoth, -, hmph, -, hlph, -, hspe, hsp, -, -⟩ := hs
  obtain ⟨-, rF, rF', rO, rfl, rfl, ⟨-, -, hFR⟩, ⟨-, -, hFR'⟩⟩ := hmv
  subst he he'
  have hap := st_c_apart W
  have hhist : ∀ Wd : Word 32 4, (Wd = C.S ∨ Wd = C.Ep) → Wd.hist m' = Wd.hist m :=
    fun Wd hWd => Word.hist_fstep (hW Wd hWd).1 hfs
      (fun l hl => by rw [(hFm l (hap Wd hWd l hl)).1]; exact (hW Wd hWd).1.cellIn hl)
      (fun l hl => by rw [(hFm l (hap Wd hWd l hl)).2])
  have hup : ∀ {α : Type} (f : γ → α), f (G' t) = f (G t) → ∀ u, f (G' u) = f (G u) :=
    fun f hf u => by
      by_cases e : u = t
      · rw [e, hf]
      · rw [hoth u e]
  have hlph' := hup L.ph hlph
  have hmph' := hup M.ph hmph
  have hspl := hup S.place.ph hspe
  have hbef := hLw.before_fstep hfs fun x h1 h2 => by
    rw [(hFm _ fun h => (st_apart W).1.not_in h ⟨rfl, h1, h2⟩).1]; exact hLw.blk.cell h1 h2
  have hx : ∀ {m : Mem} {rF : Res} {G : ThreadId → γ}, W.FreeRes G m rF →
      (rsum (W.st.cellsR m) (rsum rF rO)).gh.extent W.st.b = rO.gh.extent W.st.b :=
    fun {_ rF _} hf => by
      show ECell.unit.add ((rF.gh.extent _).add (rO.gh.extent _)) = _
      rw [hf.extent, ECell.unit_add, ECell.unit_add]
  exact {
    winv := hI'
    sub := hsub'
    win := hu.win.keep (fun u => congrArg Prod.fst (hspl u)) (hhist _ (.inl rfl))
      (hhist _ (.inr rfl))
      (hu.win.ehb.step
        (fun _ hc => hc.mono (fun u hh => .inl (by rw [hlph' u]; exact hh)) hfs.clock hbef
          hfs.threads fun u hg => by rwa [hlph' u] at hg)
        (.inl (hhist _ (.inr rfl))))
    shares := hsh
    pin := by
      have h := hu.pin
      unfold Res.Pins at h ⊢
      rw [hx hFR']; rwa [hx hFR] at h
    wt := fun u hq => by
      by_cases e : u = t
      · have hso : S.ph (G' t) = .out :=
          (congrArg Prod.snd hspe).trans (congrArg Prod.snd hsp)
        rw [e, hso] at hq; cases hq
      · rw [hoth u e] at hq ⊢; exact hu.wt u hq
    nap := fun u hq => by
      rw [hmph' u]
      rw [hlph' u, hspl u] at hq
      exact hu.nap u hq
    live := fun l hl => hM'.rest_live ((Res.owned_sep rfl rfl).mpr (.inr hl)) }

/-! ## The relabels around the other lock's code -/

/-- **A relabel of one thread in the same memory keeps the base**: its places in the rwlock's,
the condition's and the semaphore's code, its client part and its part stay; at the outer mutex
it does not end, and a writer keeps its hold; at the semaphore's mutex its place stays, or moves
between `out` and `away` out of the semaphore's code (`hl`); and its new places keep `nap`. -/
theorem relabel {t : ThreadId} {g' : γ} (hu : W.Base Sz K G rX m)
    (hwp : W.place.ph g' = W.place.ph (G t)) (hx : W.x g' = W.x (G t))
    (hpart : M.part g' = M.part (G t)) (hgone : M.ph g' ≠ .gone → M.ph (G t) ≠ .gone)
    (hwm : (W.ph (G t)).isW = true → (M.ph g').held = true)
    (hl : L.ph g' = L.ph (G t) ∨ ((L.ph (G t) = .out ∨ L.ph (G t) = .away) ∧
      (L.ph g' = .out ∨ L.ph g' = .away) ∧ S.place.ph (G t) = (.out, .out)))
    (hnap : (L.ph g' ≠ .out ∧ L.ph g' ≠ .away ∧ L.ph g' ≠ .gone) ∨
        S.place.ph (G t) ≠ (.out, .out) →
      M.ph g' = .away ∨ M.ph g' = .holdsAway) :
    W.Base Sz K (upd G t g') rX m := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have wph : W.ph g' = W.ph (G t) := congrArg Prod.fst hwp
  have spl : S.place.ph g' = S.place.ph (G t) := congrArg Prod.snd hwp
  have cph : C.ph g' = C.ph (G t) := congrArg Prod.fst spl
  have sph : S.ph g' = S.ph (G t) := congrArg Prod.snd spl
  have hup : ∀ {α : Type} (f : γ → α), f g' = f (G t) → ∀ u, f (upd G t g' u) = f (G u) :=
    fun f hf u => by
      by_cases e : u = t
      · rw [e, upd_self, hf]
      · rw [upd_ne _ _ e]
  have hwph := hup W.ph wph
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m.clocks[u]!) = true := fun _ => VClock.le_refl _
  have hpv : S.cnt (upd G t g') = S.cnt G := cnt_congr hwph
  have hmgone : ∀ u, M.ph (upd G t g' u) ≠ .gone → M.ph (G u) ≠ .gone := fun u hg => by
    by_cases e : u = t
    · rw [e, upd_self] at hg; rw [e]; exact hgone hg
    · rwa [upd_ne _ _ e] at hg
  -- the semaphore's mutex: `t` keeps its place, or moves between `out` and `away`
  have hheld : ∀ u, (L.ph (G u)).held = true → (L.ph (upd G t g' u)).held = true := fun u hh => by
    by_cases e : u = t
    · rw [e] at hh; rw [e, upd_self]
      rcases hl with e' | ⟨h1, -, -⟩
      · rw [e']; exact hh
      · rcases h1 with h1 | h1 <;> rw [h1] at hh <;> cases hh
    · rwa [upd_ne _ _ e]
  have hlgone : ∀ u, L.ph (upd G t g' u) ≠ .gone → L.ph (G u) ≠ .gone := fun u hg => by
    by_cases e : u = t
    · rw [e, upd_self] at hg; rw [e]
      rcases hl with e' | ⟨h1, -, -⟩
      · rwa [e'] at hg
      · rcases h1 with h1 | h1 <;> rw [h1] <;> exact nofun
    · rwa [upd_ne _ _ e] at hg
  have hbusy : L.ph g' = L.ph (G t) ∨ C.ph (G t) = .out ∧ S.ph (G t) = .out :=
    hl.imp id fun h => ⟨congrArg Prod.fst h.2.2, congrArg Prod.snd h.2.2⟩
  exact {
    winv := hu.winv.keep (hu.winv.ok.anti hmgone) rfl rfl rfl hwph (hup W.x hx)
      (fun u hw => by
        by_cases e : u = t
        · rw [e] at hw; rw [e, upd_self]; exact hwm hw
        · rw [upd_ne _ _ e]; exact hu.winv.wm u hw)
      fun _ _ _ _ ho e he hT => by
        rcases ho e he hT with h | h | ⟨hw, hs, u, hu', hcu⟩
        · exact .inl (LockWord.LiveLe.weaken hmgone h)
        · exact .inr (.inl h)
        · exact .inr (.inr ⟨hw, hs, u, by rw [hwph u]; exact hu', hcu⟩)
    sub := ⟨⟨hC.other (t := t) (g' := g') cph
        (fun hb => by
          rcases hbusy with e | ⟨e, -⟩
          · exact e
          · rw [e] at hb; cases hb)
        (fun hr ha => by
          rcases hbusy with e | ⟨e, -⟩
          · rw [e]; exact ha
          · rw [e] at hr; cases hr)
        (by rw [S.sx_iff, S.sx_iff, sph]; exact id) rfl rfl rfl rfl rfl
        (fun w hw _ => .inl hw) (fun _ _ _ h => h) (Nat.le_refl _) hcl, hW⟩,
      hS.mono (G' := upd G t g') (hup S.ph sph) (hup C.ph cph) hpv
        (fun u hp => by
          by_cases e : u = t
          · rw [e] at hp; rw [e, upd_self]
            rcases hbusy with e' | ⟨-, e'⟩
            · rw [e']; exact hS.pst t hp
            · rw [e'] at hp; cases hp
          · rw [upd_ne _ _ e]; exact hS.pst u hp)
        (fun u hh => .inl (hheld u hh)) hcl (fun _ h => h) rfl hlgone (fun w hw => .inl hw) rfl
        rfl⟩
    win := hu.win.keep (hup C.ph cph) rfl rfl (hu.win.ehb.step
      (fun _ hc => hc.mono (fun u hh => .inl (hheld u hh)) hcl (fun _ h => h) rfl hlgone)
      (.inl rfl))
    shares := hu.shares.congr hwph (fun _ hv => hv) fun v l => by rw [hup M.part hpart]
    pin := hu.pin
    wt := fun u hq => by rw [hwph u]; exact hu.wt u (by rwa [hup S.ph sph u] at hq)
    nap := fun u hq => by
      by_cases e : u = t
      · rw [e, upd_self] at hq ⊢; rw [spl] at hq; exact hnap hq
      · rw [upd_ne _ _ e] at hq ⊢; exact hu.nap u hq
    live := hu.live }

/-- **A relabel of one thread's place at the outer mutex keeps the base** (`relabel` at
`M.set g q h`): the thread has not ended, a writer keeps its hold (`hwm`), and the new place
keeps `nap` (`hnap`). -/
theorem relabelM (hpm : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g) {t : ThreadId} {g : γ}
    {q : LPh} {h : Res} (hu : W.Base Sz K (upd G t g) rX m) (hgone : M.ph g ≠ .gone)
    (hwm : (W.ph g).isW = true → q.held = true)
    (hnap : (L.ph g ≠ .out ∧ L.ph g ≠ .away ∧ L.ph g ≠ .gone) ∨ S.place.ph g ≠ (.out, .out) →
      q = .away ∨ q = .holdsAway) :
    W.Base Sz K (upd G t (M.set g q h)) rX m := by
  have h' := hu.relabel (t := t) (g' := M.set g q h)
    (by rw [upd_self]; exact hpm _ _ _) (by rw [upd_self]; exact W.x_m _ _ _)
    (by rw [upd_self]; exact M.part_set _ _ _) (fun _ => by rw [upd_self]; exact hgone)
    (fun hw => by rw [upd_self] at hw; rw [M.ph_set]; exact hwm hw)
    (.inl (by rw [upd_self]; exact W.pair.ph_ab _ _ _))
    (fun hq => by rw [upd_self, W.pair.ph_ab] at hq; rw [M.ph_set]; exact hnap hq)
  rwa [upd_upd] at h'

/-- **The writer naps at the outer mutex** before the semaphore's wait (`Fits.ofProduct`'s
`mnap`). -/
theorem mnap (hpm : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g) {t : ThreadId} {g : γ}
    (hm : M.ph g = .holds) (hu : W.Base Sz K (upd G t g) rX m) :
    W.Base Sz K (upd G t (M.set g .holdsAway (M.held g))) rX m :=
  hu.relabelM hpm (by rw [hm]; exact nofun) (fun _ => rfl) fun _ => .inr rfl

/-- **The writer wakes at the outer mutex** after the semaphore's wait (`Fits.ofProduct`'s
`munnap`): at `wr` out of the semaphore's mutex's code it is out of the semaphore's (`sout`). -/
theorem munnap (hpm : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g) {t : ThreadId} {g : γ}
    (hw : W.ph g = .wr) (hl : L.ph g = .out) (hm : M.ph g = .holdsAway)
    (hu : W.Base Sz K (upd G t g) rX m) :
    W.Base Sz K (upd G t (M.set g .holds (M.held g))) rX m := by
  have hso := hu.sout (u := t) (by rw [upd_self]; exact hl) (by rw [upd_self, hw]; exact nofun)
  rw [upd_self] at hso
  exact hu.relabelM hpm (by rw [hm]; exact nofun) (fun _ => rfl) fun hq => by
    rcases hq with ⟨hq, -⟩ | hq
    · exact absurd hl hq
    · exact absurd hso hq

/-- **The last reader goes `away` from the outer mutex** around its post at the semaphore
(`Fits.ofProduct`'s `maway`). -/
theorem maway (hpm : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g) {t : ThreadId} {g : γ}
    (hm : M.ph g = .out) (hu : W.Base Sz K (upd G t g) rX m) :
    W.Base Sz K (upd G t (M.set g .away rnil)) rX m := by
  have hnw := hu.winv.not_isW (u := t) (by rw [upd_self]; exact .inl hm)
  rw [upd_self] at hnw
  exact hu.relabelM hpm (by rw [hm]; exact nofun) (fun hw => by rw [hnw] at hw; cases hw)
    fun _ => .inl rfl

/-- **The last reader comes back from `away`** at the outer mutex (`Fits.ofProduct`'s
`munaway`): out of the semaphore's mutex's code it is out of the semaphore's (`sout`; it is no
writer at `ww`, which holds the outer mutex). -/
theorem munaway (hpm : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g) {t : ThreadId} {g : γ}
    (hm : M.ph g = .away) (hl : L.ph g = .out) (hu : W.Base Sz K (upd G t g) rX m) :
    W.Base Sz K (upd G t (M.set g .out rnil)) rX m := by
  have hnw := hu.winv.not_isW (u := t) (by rw [upd_self]; exact .inr hm)
  have hso := hu.sout (u := t) (by rw [upd_self]; exact hl)
    (fun e => by rw [e] at hnw; cases hnw)
  rw [upd_self] at hnw hso
  exact hu.relabelM hpm (by rw [hm]; exact nofun) (fun hw => by rw [hnw] at hw; cases hw)
    fun hq => by
      rcases hq with ⟨hq, -⟩ | hq
      · exact absurd hl hq
      · exact absurd hso hq

/-- **A relabel between `out` and `away` at the semaphore's mutex** around the outer mutex's
code (`Fits.ofProduct`'s `laway`, `lunaway`): the thread is out of the outer mutex's code or
holds it awake, so it is out of the semaphore's code (`sout_of_m`). -/
theorem lmove (hpl : ∀ g q h, S.place.ph (L.set g q h) = S.place.ph g) {t : ThreadId} {g : γ}
    {q : LPh} (hl : L.ph g = .out ∨ L.ph g = .away) (hq : q = .out ∨ q = .away)
    (hm : M.ph g = .out ∨ M.ph g = .holds) (hu : W.Base Sz K (upd G t g) rX m) :
    W.Base Sz K (upd G t (L.set g q rnil)) rX m := by
  have hso := hu.sout_of_m (u := t) (by rw [upd_self]; exact hm)
  have h := hu.relabel (t := t) (g' := L.set g q rnil)
    (by rw [upd_self]; exact Prod.ext (W.ph_l _ _ _) (hpl _ _ _))
    (by rw [upd_self]; exact W.x_l _ _ _)
    (by rw [upd_self, W.pair.part, L.part_set, ← W.pair.part])
    (fun hg => by rw [upd_self]; rwa [W.pair.ph_ba] at hg)
    (fun hw => by
      rw [W.pair.ph_ba]
      have := hu.winv.wm t hw
      rwa [upd_self] at this)
    (.inr ⟨by rw [upd_self]; exact hl, by rw [L.ph_set]; exact hq, hso⟩)
    (fun hn => by
      rcases hn with ⟨h1, h2, -⟩ | hn
      · rw [L.ph_set] at h1 h2
        rcases hq with e | e
        · exact absurd e h1
        · exact absurd e h2
      · exact absurd hso hn)
  rwa [upd_upd] at h

/-- **The tick obligation of the outer mutex's view** (`fitsM`'s `tick`). -/
theorem tickM (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g) :
    FLock.Pair.TickKeeps M L (W.Base Sz K) := by
  intro t G sB rL rH rX m r hg hsB hk hM hM' hu
  exact hu.tick hM hM' (fun _ => rfl) (hM.w.live t hg).1 hpl

/-- **The tick obligation of the semaphore's view** (`fitsS`'s `tick`): the outer mutex's
invariant before and after the tick is the product's (`FLock.Pair.swap`; the outer mutex stays
kept over the tick, `FLock.Pair.Keeps.partStep`), at the common rest beside the semaphore's mutex's
side, which holds no share (`FLock.Keeps.side_share`, `lR_share`). -/
theorem tickL (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g) :
    FLock.Pair.TickKeeps L M (W.Base Sz K) := by
  intro t G sB rL rH rX m r hg hsB hk hL hL' hu
  have hRM : ∀ G, (M.R G).Unshared := fun G => by rw [W.mR]; exact FAssn.Unshared.emp
  have hpart : L.setPart (G t) r = M.setPart (G t) r := (W.pair.setPart _ _).symm
  rw [hpart] at hL' ⊢
  obtain ⟨rLL, rHL, hMi, hkL⟩ := W.pair.symm.swap (FLock.Pair.inv_side hL hsB) hk
    (FLock.NoGatherHeld.of_R hRM hk.facts)
  obtain ⟨hsB', hk'⟩ := FLock.Pair.Keeps.partStep (hO := Heap.empty) W.pair.symm hk hsB
    (FStepIn.ticked m _).reads hL' (M.ph_setPart _ _) (M.held_setPart _ _)
    (fun r' h => (M.R_setPart G t r r').mpr h) hk.xdisj hk.xoff
  obtain ⟨rLL', rHL', hMi', hkL'⟩ := W.pair.symm.swap (FLock.Pair.inv_side hL' hsB') hk'
    (FLock.NoGatherHeld.of_R hRM hk'.facts)
  exact hu.tick hMi hMi'
    (fun l => by rw [hkL'.side_share (lR_share W l), hkL.side_share (lR_share W l)])
    (hL.w.live t hg).1 hpl

/-! ## A step of the semaphore's code -/

/-- **The base at the rest after a step of the semaphore's code** (`FCond.StepRest`; what the
cases of `sstep` share). The step changes only `t`'s ghost value and keeps its place at the outer
mutex; the case gives the condition's and the semaphore's invariants and the window after it, the
rwlock's invariant after it at every rest within the rest before it (`hinv`, for
`Inv.stepRest`), the words valid after it (`hok`), the memory at a byte of the words whose cell
the rest keeps (`hE`, for `FCond.StepRest.words`), the rest's other bytes live (`hlv`), the
shares, and `t`'s new places for `wt` and `nap`. -/
theorem ofStepRest {t : ThreadId} {G' : ThreadId → γ} {rX' : Res} {m' : Mem}
    (hu : W.Base Sz K G rX m) (hsh : C.StepRest m m' rX rX')
    (hRoff : ∀ xs r l, W.R xs r → (C.S.In l ∨ C.Ep.In l) → r.heap l = none)
    (hCI' : C.Inv L G' m') (hSI' : S.Inv G' m') (hwin : C.Win1 L G' m')
    (hoth : ∀ u, u ≠ t → G' u = G u) (hmph : M.ph (G' t) = M.ph (G t))
    (hinv : ∀ rZ, W.Inv G rZ m → (∀ l, rZ.owned l ≠ none → rX.owned l ≠ none) →
      (∀ l, rZ.heap l ≠ none → rX.heap l ≠ none) → W.Inv G' rZ m')
    (hok : ∀ V : Word 32 4, (V = C.S ∨ V = C.Ep) → V.Ok m' fun _ => True)
    (hE : ∀ l, (C.S.In l ∨ C.Ep.In l) → rX'.heap l = rX.heap l → m'.heap l = m.heap l)
    (hlv : ∀ l, ¬ (C.S.In l ∨ C.Ep.In l) → rX.owned l ≠ none → rX'.owned l ≠ none →
      m'.heap l ≠ none)
    (hshr : W.Shares G' m') (hwt : S.ph (G' t) = .wt → W.ph (G' t) = .ww)
    (hnap : (L.ph (G' t) ≠ .out ∧ L.ph (G' t) ≠ .away ∧ L.ph (G' t) ≠ .gone) ∨
        S.place.ph (G' t) ≠ (.out, .out) →
      M.ph (G t) = .away ∨ M.ph (G t) = .holdsAway) : W.Base Sz K G' rX' m' := by
  obtain ⟨⟨-, hW⟩, -⟩ := hu.sub
  exact {
    winv := hu.winv.stepRest hsh hRoff hinv
    sub := ⟨⟨hCI', fun V hV => ⟨hok V hV, hsh.words hV (hW V hV).2 hE⟩⟩, hSI'⟩
    win := hwin
    shares := hshr
    pin := hu.pin.of_gh hsh.gh
    wt := fun u hq => by
      by_cases e : u = t
      · rw [e] at hq ⊢; exact hwt hq
      · rw [hoth u e] at hq ⊢; exact hu.wt u hq
    nap := fun u hq => by
      by_cases e : u = t
      · rw [e] at hq ⊢; rw [hmph]; exact hnap hq
      · rw [hoth u e] at hq ⊢; exact hu.nap u hq
    live := fun l hl => by
      by_cases hw : C.S.In l ∨ C.Ep.In l
      · obtain ⟨V, hV, h⟩ := FCond.word_of hw
        exact (hok V hV).cellIn h
      · exact hlv l hw (hsh.owned hw hl) hl }

/-- **A step in the frame of the semaphore's mutex's view** (its word and its rest, the outer
mutex's side `sB` next to the common rest, read at the partial shares of `t`'s part and held
resource: a step on `t`'s own part, the holder's step `FSem.Move.hold`), with the mutex's
invariant before and after it and the words' cells kept up to `Cell.norm` (`hnorm`). The rwlock's
invariant stays at every rest within the common rest (`Inv.stepIn`: the state word's cells stay
exactly, by the pin; the step reads a byte of the readers' heap only as a reader, `Shares.hrd`);
the words stay valid; and a byte of the words whose cell the rest keeps is the memory's
(`FLock.Inv.cell_pinned`). -/
theorem natStep {t : ThreadId} {G' G'' : ThreadId → γ} {sB rL rH rX' : Res} {m' : Mem}
    (hu : W.Base Sz K G rX m) (hsh : C.StepRest m m' rX rX')
    (hsB : Res.Sim sB (FLock.side M m rL rH)) (hk : M.Keeps G m rL rH rX)
    (hL : L.Inv G (rsum sB rX) m) (hL' : L.Inv G'' (rsum sB rX') m') (hcur : m.current = t)
    (hlg : L.ph (G t) ≠ .gone)
    (hfs : FStepIn (rsum (L.wordR m) (rsum sB rX)).owned m m'
      ((rsum (L.wordR m) (rsum sB rX)).shared.inter (rsum (L.part (G t)) (L.held (G t))).shared))
    (hnorm : ∀ V : Word 32 4, (V = C.S ∨ V = C.Ep) → ∀ l, V.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hph : ∀ u, W.ph (G' u) = W.ph (G u)) (hx : ∀ u, W.x (G' u) = W.x (G u))
    (hmph : ∀ u, M.ph (G' u) = M.ph (G u)) :
    (∀ rZ, W.Inv G rZ m → (∀ l, rZ.owned l ≠ none → rX.owned l ≠ none) →
      (∀ l, rZ.heap l ≠ none → rX.heap l ≠ none) → W.Inv G' rZ m') ∧
    (∀ V : Word 32 4, (V = C.S ∨ V = C.Ep) → V.Ok m' fun _ => True) ∧
    ∀ l, (C.S.In l ∨ C.Ep.In l) → rX'.heap l = rX.heap l → m'.heap l = m.heap l := by
  obtain ⟨⟨-, hW⟩, -⟩ := hu.sub
  have hpin' : rX'.Pins W.st.b Sz K := hu.pin.of_gh hsh.gh
  have hsBn : ∀ l, rX.heap l ≠ none → sB.heap l = none := fun l h =>
    (hsB.disj hk.side_disj l).resolve_right h
  -- a byte of the lock's block that the rest holds with its cell before and after the step
  have hpinE : ∀ l c, l.1 = W.st.b → m.heap l = some c → rX.heap l = some ⟨c, none⟩ →
      rX'.heap l = rX.heap l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ c hb hc hr hr'
    obtain rfl : b = W.st.b := hb
    refine hL.cell_pinned hL' (Res.Pins.right hu.pin) (Res.Pins.right hpin') hc ?_
    have e1 := hsBn (W.st.b, x) (by rw [hr]; nofun)
    show (sB.heap (W.st.b, x)).or (rX'.heap (W.st.b, x)) = some ⟨c, none⟩
    rw [e1, hr', hr]; rfl
  have hcellX : ∀ V : Word 32 4, (V = C.S ∨ V = C.Ep) → ∀ l, V.In l → ∀ c, m.heap l = some c →
      rX.heap l = some ⟨c, none⟩ := fun V hV l hl c hc => by
    obtain ⟨-, rY, e, -⟩ := hW V hV
    rw [e]
    show ((cellsAt V.In m).heap l).or (rY.heap l) = _
    rw [cellsAt_of hl, hc]; rfl
  have hE : ∀ l, (C.S.In l ∨ C.Ep.In l) → rX'.heap l = rX.heap l → m'.heap l = m.heap l :=
    fun l hl hr => by
      obtain ⟨V, hV, hlV⟩ := FCond.word_of hl
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp ((hW V hV).1.cellIn hlV)
      exact hpinE l c (hlV.1.trans (c_blk W V hV)) hc (hcellX V hV l hlV c hc) hr
  have hstc : ∀ l, W.st.In l → m'.heap l = m.heap l := fun l hl => by
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hu.winv.ok.cellIn hl)
    refine hpinE l c hl.1 hc ?_ (hsh.heap fun h => ?_)
    · obtain ⟨rF, rO, e, -⟩ := hu.winv.rest
      rw [e]
      show ((cellsAt W.st.In m).heap l).or _ = _
      rw [cellsAt_of hl, hc]; rfl
    · obtain ⟨V, hV, h⟩ := FCond.word_of h
      exact st_c_apart W V hV l h hl
  have hXh : ∀ l, rX.heap l ≠ none → (rsum (L.wordR m) (rsum sB rX)).heap l ≠ none :=
    fun l h e => h (rsum_heap_none.mp (rsum_heap_none.mp e).2).2
  have hRn : ∀ l, rX.heap l ≠ none → ((rsum (L.wordR m) (rsum sB rX)).shared.inter
      (rsum (L.part (G t)) (L.held (G t))).shared) l = none := fun l h =>
    Heap.inter_none (Res.excl_shared_disj (Res.excl_of_heap (hXh l h)))
  have hXo : ∀ l, rX.owned l ≠ none → (rsum (L.wordR m) (rsum sB rX)).owned l ≠ none :=
    fun l h => (Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inr h)))
  refine ⟨fun rZ hIZ ho hh => hIZ.stepIn hfs (fun l h => hXo l (ho l h))
      (fun l h => hu.live l (ho l h)) hstc (fun l h => hRn l (hh l h))
      (hu.shares.hrd (rh := L.held (G m.current)) (by rw [hcur]; exact (hL.w.live t hlg).2)
        (fun l => hL.held_share (lR_share W l) m.current)
        fun l h => by rw [hcur, W.pair.part]; exact (Heap.inter_ne.mp h).2)
      hph hx (fun u h => by rwa [hmph u] at h) (fun u h => by rw [hmph u]; exact hu.winv.wm u h),
    fun V hV => ?_, hE⟩
  -- the word stays valid: the step in the frame of its cells
  have hVx : ∀ l, (V.cellsR m).owned l ≠ none → rX.heap l ≠ none := fun l h => by
    have hl : V.In l := Classical.byContradiction fun hn => h (cellsAt_owned_none hn)
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp ((hW V hV).1.cellIn hl)
    rw [hcellX V hV l hl c hc]; nofun
  exact (hW V hV).1.fstep
    (hfs.weakenR (fun l h => hXo l (Res.owned_of_heap (hVx l h)))
      fun l h hr => absurd (hRn l (hVx l h)) hr)
    (fun l hl => Res.owned_of_heap (cellsAt_some hl ((hW V hV).1.cellIn hl))) (hnorm V hV)

/-- **A step of the semaphore's code keeps the base** (`fitsS`'s `kstep`; `FSem.prim`'s `Step`
in the semaphore's mutex's view, whose rest is the outer mutex's side `sB` next to the common
rest, which after the step is `FCond.StepRest`'s):
- a step of the condition's code at one of its words (`FCond.MStep`): the rwlock's invariant by
  `Inv.mstep`, the words by `FCond.MStep.word_rmw`, and the memory at the word's bytes by the
  rest's two equations when the rest keeps their cells;
- a step on `t`'s own part and the holder's step (`natStep`); the own part's new shares by
  counting in the outer mutex's view (`Shares.keep`, as `tickL`);
- the waiter's entry into the condition's wait, a relabel: only the writer at `ww` waits at the
  semaphore (`wt`, `Inv.one`), so no thread is registered (`FSem.Win1.semStep`'s `hent`).

The client gives that no resource with `R` has a cell at the condition's words (`hRoff`) and the
laws of the semaphore's places next to both mutexes. -/
theorem sstep {t : ThreadId} {G' : ThreadId → γ} {rS rS' sB rL rH rX' : Res} {m' : Mem}
    (hu : W.Base Sz K G rX m) (hs : S.prim.Step t G rS m G' rS' m') (he : rS = rsum sB rX)
    (he' : rS' = rsum sB rX') (hsh : C.StepRest m m' rX rX')
    (hsB : Res.Sim sB (FLock.side M m rL rH)) (hk : M.Keeps G m rL rH rX)
    (hk' : M.Keeps G' m' rL rH rX')
    (hRoff : ∀ xs r l, W.R xs r → (C.S.In l ∨ C.Ep.In l) → r.heap l = none)
    (mph_s : ∀ g q, M.ph (S.place.set g q) = M.ph g)
    (lph : ∀ g q, L.ph (S.place.set g q) = L.ph g)
    (lpart : ∀ g q, L.part (S.place.set g q) = L.part g)
    (ph_l : ∀ g q h, S.place.ph (L.set g q h) = S.place.ph g)
    (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g) :
    W.Base Sz K G' rX' m' := by
  subst he
  obtain ⟨⟨-, hW⟩, hS⟩ := hu.sub
  have hsubL : S.prim.Sub G (rsum sB rX) m :=
    ⟨FPrim.ofWords_sub_rsum hu.sub.1 (hsB.disj hk.side_disj), hS⟩
  have sph_l : ∀ g q h, S.ph (L.set g q h) = S.ph g := fun g q h => congrArg Prod.snd (ph_l g q h)
  have ph_part : ∀ g r, S.place.ph (L.setPart g r) = S.place.ph g := fun g r => by
    rw [← W.pair.setPart]; exact congrArg Prod.snd (hpl g r)
  -- a coordinate that the semaphore's places leave, over the condition's and the semaphore's
  have hc : ∀ {α : Type} (f : γ → α), (∀ g q, f (S.place.set g q) = f g) →
      ∀ g p, f (C.set g p) = f g := fun f hf g p => by rw [← S.place_c]; exact hf g _
  have hss : ∀ {α : Type} (f : γ → α), (∀ g q, f (S.place.set g q) = f g) →
      ∀ g s, f (S.set g s) = f g := fun f hf g s => by rw [← S.place_s]; exact hf g _
  have sph_c : ∀ g p, S.ph (C.set g p) = S.ph g := fun g p => by
    rw [← S.place_c]; exact congrArg Prod.snd (S.place.ph_set g (p, S.ph g))
  have mpart : ∀ g g' : γ, L.part g' = L.part g → M.part g' = M.part g := fun g g' h => by
    rw [W.pair.part, W.pair.part]; exact h
  have hall : ∀ {α : Type} (f : γ → α) {g' : γ}, f g' = f (G t) →
      ∀ u, f (upd G t g' u) = f (G u) := fun f _ hf u => by
    by_cases e : u = t
    · rw [e, upd_self, hf]
    · rw [upd_ne _ _ e]
  -- the window: no thread is registered when the writer at `ww` enters the wait
  have hwin : C.Win1 L G' m' := FSem.Win1.semStep hu.win hsubL ph_l ph_part lph
    (fun Wd hWd => (c_apart W Wd hWd).1)
    (fun _ hst hwx hct u => by
      cases e : (C.ph (G u)).isReg with
      | false => rfl
      | true =>
        have hwu : W.ph (G u) = .ww := hu.wt u (hS.wt u (CPh.isReg_waits e))
        have hwt : W.ph (G t) = .ww := (W.wx_iff _).mp hwx
        have hut : u = t := hu.winv.one u t (by rw [hwu]; rfl) (by rw [hwt]; rfl)
        rw [hut, hct] at e; cases e)
    hs
  have hRM : ∀ G, (M.R G).Unshared := fun G => by rw [W.mR]; exact FAssn.Unshared.emp
  have hsBn : ∀ l, rX.heap l ≠ none → sB.heap l = none := fun l h =>
    (hsB.disj hk.side_disj l).resolve_right h
  rcases hs with ⟨hSI', hcs | ⟨hCI', hmv⟩⟩
  · subst he'
    obtain ⟨Wd, rY, hWs, heq, heq', hY, hCI', hcase⟩ := hcs
    rcases hcase with ⟨p, q, h, ⟨-, hq, hms, -, -⟩, -, rfl⟩ |
      ⟨r, hown, hL, hcur, hfs, hcW, -, -, hL', hG'⟩
    · -- a step of the condition's code at the word `Wd`
      have hgw : W.ph (L.set (C.set (G t) p) q h) = W.ph (G t) :=
        (W.ph_l _ _ _).trans (hc W.ph W.ph_sp _ _)
      have hgm : M.ph (L.set (C.set (G t) p) q h) = M.ph (G t) :=
        (W.pair.ph_ba _ _ _).trans (hc M.ph mph_s _ _)
      have hgp : M.part (L.set (C.set (G t) p) q h) = M.part (G t) :=
        mpart _ _ ((L.part_set _ _ _).trans (hc L.part lpart _ _))
      have hgx : W.x (L.set (C.set (G t) p) q h) = W.x (G t) := (W.x_l _ _ _).trans (W.x_c _ _)
      have hsph : S.ph (L.set (C.set (G t) p) q h) = S.ph (G t) :=
        (sph_l _ _ _).trans (sph_c _ _)
      have hlq : L.ph (L.set (C.set (G t) p) q h) = q := L.ph_set _ _ _
      have hwph := hall W.ph hgw
      have hmph := hall M.ph hgm
      have hpart := hall M.part hgp
      have hin : ∀ l, Wd.In l → C.S.In l ∨ C.Ep.In l := fun l hl => FCond.in_words hWs hl
      refine hu.ofStepRest hsh hRoff hCI' hSI' hwin (fun u e => upd_ne _ _ e)
        (by rw [upd_self]; exact hgm)
        (fun rZ hIZ ho _ =>
          (hIZ.mstep hms hWs hRoff fun l h => hu.live l (ho l h)).congr hwph hmph (hall W.x hgx))
        (fun V hV => (hms.word_rmw (hW V hV).1 (FCond.words_apart hV hWs)
          (FCond.words_apart hV (.inr rfl))).1)
        (fun l _ hr => ?_) (fun l hl ho _ => ?_)
        (hu.shares.congr hwph
          (fun v hv => by rwa [LockWord.joinedB_congr hms.threads] at hv)
          fun v l => by rw [hpart v])
        (fun hq' => ?_) (fun hq' => ?_)
      · -- the word's bytes: the rest has their cells before and after the step
        by_cases hlW : Wd.In l
        · have hXne : rX.heap l ≠ none := by
            obtain ⟨hok, rA, e, -⟩ := hW Wd hWs
            rw [e]; exact fun en => cellsAt_some hlW (hok.cellIn hlW) (rsum_heap_none.mp en).1
          have e1 : (sB.heap l).or (rX.heap l) = ((cellsAt Wd.In m).heap l).or (rY.heap l) :=
            congrFun (congrArg Res.heap heq) l
          have e2 : (sB.heap l).or (rX'.heap l) = ((cellsAt Wd.In m').heap l).or (rY.heap l) :=
            congrFun (congrArg Res.heap heq') l
          rw [hsBn l hXne, hY l hlW, Option.none_or, Option.or_none] at e1 e2
          exact cellsAt_inj hlW (e2.symm.trans (hr.trans e1))
        · exact hms.cells hlW
      · rw [hms.cells fun h => hl (hin l h)]; exact hu.live l ho
      · rw [upd_self] at hq' ⊢
        rw [hgw]; exact hu.wt t (hsph.symm.trans hq')
      · rw [upd_self] at hq'
        rcases hq' with ⟨h1, h2, h3⟩ | hsp
        · rw [hlq] at h1 h2 h3
          rcases hq with ⟨rfl, -⟩ | ⟨-, hq2, -⟩
          · exact hu.nap t (.inl ⟨h1, h2, h3⟩)
          · rcases hq2 with rfl | ⟨rfl, -⟩
            · exact absurd rfl h1
            · exact absurd rfl h2
        · refine hu.nap t (.inr fun e => hsp ?_)
          have hs0 : S.ph (L.set (C.set (G t) p) q h) = .out := hsph.trans (congrArg Prod.snd e)
          have hc0 := hSI'.c_out hCI' (u := t) (by rw [upd_self]; exact hs0)
          rw [upd_self] at hc0
          exact Prod.ext hc0 hs0
    · -- a step on `t`'s own part
      rw [← W.pair.setPart] at hG'
      subst hG'
      have hlg : L.ph (G t) ≠ .gone := by rcases hown with e | e <;> rw [e] <;> nofun
      have hgw : W.ph (M.setPart (G t) r) = W.ph (G t) := congrArg Prod.fst (hpl _ _)
      have hgs : S.place.ph (M.setPart (G t) r) = S.place.ph (G t) := congrArg Prod.snd (hpl _ _)
      have hgl : L.ph (M.setPart (G t) r) = L.ph (G t) := by rw [W.pair.setPart, L.ph_setPart]
      have hsubW : (C.prim L).Sub G (rsum (Wd.cellsR m) rY) m := by rw [← heq]; exact hsubL.1
      have hLW : L.Inv G (rsum (Wd.cellsR m) rY) m := by rw [← heq]; exact hL
      have hLW' : L.Inv (upd G t (M.setPart (G t) r)) (rsum (Wd.cellsR m') rY) m' := by
        rw [← heq']; exact hL'
      obtain ⟨hinv, hok, hE⟩ := hu.natStep hsh hsB hk hL hL' hcur hlg hfs
        (FCond.cells_own hsubW hLW hLW' hcW) (hall W.ph hgw) (hall W.x (W.x_part _ _))
        (hall M.ph (M.ph_setPart _ _))
      -- the outer mutex's invariant before and after the step, for the new part's shares
      obtain ⟨hsB', -⟩ := FLock.Pair.Keeps.partStep W.pair.symm hk hsB hfs hL'
        (M.ph_setPart _ _) (M.held_setPart _ _) (fun r' h' => (M.R_setPart G t r r').mpr h')
        hk'.xdisj hk'.xoff
      obtain ⟨rLL, rHL, hMi, hkL⟩ := W.pair.symm.swap (FLock.Pair.inv_side hL hsB) hk
        (FLock.NoGatherHeld.of_R hRM hk.facts)
      obtain ⟨rLL', rHL', hMi', hkL'⟩ := W.pair.symm.swap (FLock.Pair.inv_side hL' hsB') hk'
        (FLock.NoGatherHeld.of_R hRM hk'.facts)
      refine hu.ofStepRest hsh hRoff hCI' hSI' hwin (fun u e => upd_ne _ _ e)
        (by rw [upd_self]; exact M.ph_setPart _ _) hinv hok hE
        (fun l _ _ ho' => hL'.rest_live ((Res.owned_sep rfl rfl).mpr (.inr ho')))
        (hu.shares.keep hMi hMi'
          (fun l => by
            show ((FLock.side L m' rLL' rHL').gh.share l).add (rX'.gh.share l) =
              ((FLock.side L m rLL rHL).gh.share l).add (rX.gh.share l)
            rw [hkL'.side_share (lR_share W l), hkL.side_share (lR_share W l), hsh.gh])
          (fun u q H l c hq hl => SCell.pos_add' _ (hu.winv.rest_share hq hl)) hfs.threads
          (hL.w.live t hlg).1 (fun u e => upd_ne _ _ e) (by rw [upd_self]; exact hgw))
        (fun hq' => ?_) (fun hq' => ?_)
      · rw [upd_self] at hq' ⊢
        rw [hgw]; exact hu.wt t ((congrArg Prod.snd hgs).symm.trans hq')
      · rw [upd_self, hgl, hgs] at hq'
        exact hu.nap t hq'
  · cases hmv with
    | enter _ _ hst _ _ =>
      -- the waiter's entry into the condition's wait: a relabel
      have hgw : W.ph (C.set (G t) .en) = W.ph (G t) := hc W.ph W.ph_sp _ _
      have hgm : M.ph (C.set (G t) .en) = M.ph (G t) := hc M.ph mph_s _ _
      have hgp : M.part (C.set (G t) .en) = M.part (G t) := mpart _ _ (hc L.part lpart _ _)
      have hwph := hall W.ph hgw
      have hpart := hall M.part hgp
      refine hu.ofStepRest hsh hRoff hCI' hSI' hwin (fun u e => upd_ne _ _ e)
        (by rw [upd_self]; exact hgm)
        (fun rZ hIZ _ _ => hIZ.congr hwph (hall M.ph hgm) (hall W.x (W.x_c _ _)))
        (fun V hV => (hW V hV).1) (fun _ _ _ => rfl) (fun l _ ho _ => hu.live l ho)
        (hu.shares.congr hwph (fun _ h => h) fun v l => by rw [hpart v])
        (fun _ => ?_) (fun _ => ?_)
      · rw [upd_self, hgw]; exact hu.wt t hst
      · exact hu.nap t (.inr fun e => by
          have h2 : S.ph (G t) = .out := congrArg Prod.snd e
          rw [hst] at h2; cases h2)
    | hold s h hlh _ hL hcur hfs hL'' hcells hgo =>
      -- the holder's step on the mutex's resource
      obtain ⟨G'', hL''⟩ := hL''
      rw [he'] at hL''
      have hlg : L.ph (G t) ≠ .gone := by rw [hlh]; nofun
      have hgw : W.ph (S.set (L.set (G t) .holds h) s) = W.ph (G t) :=
        (hss W.ph W.ph_sp _ _).trans (W.ph_l _ _ _)
      have hgm : M.ph (S.set (L.set (G t) .holds h) s) = M.ph (G t) :=
        (hss M.ph mph_s _ _).trans (W.pair.ph_ba _ _ _)
      have hgp : M.part (S.set (L.set (G t) .holds h) s) = M.part (G t) :=
        mpart _ _ ((hss L.part lpart _ _).trans (L.part_set _ _ _))
      have hgx : W.x (S.set (L.set (G t) .holds h) s) = W.x (G t) :=
        (W.x_s _ _).trans (W.x_l _ _ _)
      have hwph := hall W.ph hgw
      have hpart := hall M.part hgp
      obtain ⟨hinv, hok, hE⟩ := hu.natStep hsh hsB hk hL hL'' hcur hlg hfs hcells hwph
        (hall W.x hgx) (hall M.ph hgm)
      refine hu.ofStepRest hsh hRoff hCI' hSI' hwin (fun u e => upd_ne _ _ e)
        (by rw [upd_self]; exact hgm) hinv hok hE
        (fun l _ _ ho' => hL''.rest_live ((Res.owned_sep rfl rfl).mpr (.inr ho')))
        (hu.shares.congr hwph
          (fun v hv => by rwa [LockWord.joinedB_congr hfs.threads] at hv)
          fun v l => by rw [hpart v])
        (fun hq' => ?_) (fun _ => ?_)
      · rw [upd_self] at hq' ⊢
        rw [hgw]
        have h's : s = .wt := (S.ph_set _ _).symm.trans hq'
        rcases hgo with e | ⟨-, -, hwx'⟩ | ⟨e, -⟩ | ⟨e, -⟩
        · exact hu.wt t (e.symm.trans h's)
        · exact (W.wx_iff _).mp hwx'
        · rw [h's] at e; cases e
        · rw [h's] at e; cases e
      · exact hu.nap t (.inl ⟨by rw [hlh]; nofun, by rw [hlh]; nofun, by rw [hlh]; nofun⟩)

/-! ## The take and the give at the semaphore -/

/-- **A handover at the semaphore keeps the base** (what `utake` and `upost` share): `t` holds
the semaphore's mutex and changes its place at the rwlock and its part, in the same memory. Its
places at both mutexes and in the condition's code stay, it is not at the semaphore's `wt` after
it, and no thread is a reader after it (the resource is posted, before or after), so the shares'
clause is empty. The three invariants after it are given (`Inv.take`/`Inv.post`, the
semaphore's own). -/
theorem handover {t : ThreadId} {g' : γ} (hu : W.Base Sz K G rX m)
    (hI : W.Inv (upd G t g') rX m) (hS : S.Inv (upd G t g') m) (hC : C.Inv L (upd G t g') m)
    (hnr : ∀ u, (W.ph (upd G t g' u)).isRd = false) (hlh : L.ph (G t) = .holds)
    (hl : L.ph g' = L.ph (G t)) (hc : C.ph g' = C.ph (G t)) (hs : S.ph g' ≠ .wt)
    (hm : M.ph g' = M.ph (G t)) : W.Base Sz K (upd G t g') rX m := by
  have hup : ∀ {α : Type} (f : γ → α), f g' = f (G t) → ∀ u, f (upd G t g' u) = f (G u) :=
    fun f hf u => by
      by_cases e : u = t
      · rw [e, upd_self, hf]
      · rw [upd_ne _ _ e]
  exact {
    winv := hI
    sub := ⟨⟨hC, hu.sub.1.2⟩, hS⟩
    win := hu.win.keep (hup C.ph hc) rfl rfl (hu.win.ehb.relabel (hup L.ph hl))
    shares := fun u q H hq => by
      have h := hnr u
      rw [hq] at h; cases h
    pin := hu.pin
    wt := fun u hq => by
      by_cases e : u = t
      · rw [e, upd_self] at hq; exact absurd hq hs
      · rw [upd_ne _ _ e] at hq ⊢; exact hu.wt u hq
    nap := fun u hq => by
      by_cases e : u = t
      · rw [e, upd_self, hm]
        exact hu.nap t (.inl ⟨by rw [hlh]; nofun, by rw [hlh]; nofun, by rw [hlh]; nofun⟩)
      · rw [upd_ne _ _ e] at hq ⊢; exact hu.nap u hq
    live := hu.live }

/-- A coordinate that the semaphore's places leave, over the semaphore's own place. -/
theorem of_sset {α : Type} {f : γ → α} (hf : ∀ g q, f (S.place.set g q) = f g) (g : γ) (s : SPh) :
    f (S.set g s) = f g := by
  rw [← S.place_s]; exact hf g _

/-- The rwlock's place of a holder of the semaphore's mutex at a place of the semaphore. -/
theorem wph_hold (g : γ) (h : Res) (s : SPh) : W.ph (S.set (L.set g .holds h) s) = W.ph g := by
  rw [of_sset W.ph_sp, W.ph_l]

/-- The places of the rwlock, the condition and the semaphore over a thread's part. -/
theorem place_lpart (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g) (g : γ) (r : Res) :
    W.place.ph (L.setPart g r) = W.place.ph g := by
  rw [← W.pair.setPart]; exact hpl g r

section
variable (mph_s : ∀ g q, M.ph (S.place.set g q) = M.ph g)
  (lph : ∀ g q, L.ph (S.place.set g q) = L.ph g)
  (ph_l : ∀ g q h, S.place.ph (L.set g q h) = S.place.ph g)
include mph_s

/-- The outer mutex's place of a holder of the semaphore's mutex at a place of the semaphore. -/
theorem mph_hold (W : FRw γ X Y M L C S) (g : γ) (h : Res) (s : SPh) :
    M.ph (S.set (L.set g .holds h) s) = M.ph g := by
  rw [of_sset mph_s, W.pair.ph_ba]

include lph ph_l

/-- **A handover of a holder at the semaphore's `pst`** (`handover` at the places of `utake` and
`upost`): `t` goes from `g` to `g₀` under its hold of the semaphore's mutex, where `g₀` keeps
the places at the outer mutex and in the condition's code. -/
theorem handoverS {t : ThreadId} {g g₀ : γ} {h₁ h₂ : Res} {sh sc}
    (hu : W.Base Sz K (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m)
    (hI : W.Inv (upd G t (S.set (L.set g₀ .holds h₂) (.pst sh sc))) rX m)
    (hS : S.Inv (upd G t (S.set (L.set g₀ .holds h₂) (.pst sh sc))) m)
    (hC : C.Inv L (upd G t (S.set (L.set g₀ .holds h₂) (.pst sh sc))) m)
    (hnr : ∀ u, (W.ph (upd G t (S.set (L.set g₀ .holds h₂) (.pst sh sc)) u)).isRd = false)
    (hm : M.ph g₀ = M.ph g) (hc : C.ph g₀ = C.ph g) :
    W.Base Sz K (upd G t (S.set (L.set g₀ .holds h₂) (.pst sh sc))) rX m := by
  have lph_hold : ∀ g h s, L.ph (S.set (L.set g .holds h) s) = .holds := fun g h s => by
    rw [of_sset lph, L.ph_set]
  have cph_hold : ∀ g h s, C.ph (S.set (L.set g .holds h) s) = C.ph g := fun g h s => by
    rw [← S.place_s]
    exact (congrArg Prod.fst (S.place.ph_set _ _)).trans (congrArg Prod.fst (ph_l g .holds h))
  have h := hu.handover (t := t) (g' := S.set (L.set g₀ .holds h₂) (.pst sh sc))
    (by rw [upd_upd]; exact hI) (by rw [upd_upd]; exact hS) (by rw [upd_upd]; exact hC)
    (fun u => by rw [upd_upd]; exact hnr u) (by rw [upd_self, lph_hold])
    (by rw [upd_self, lph_hold, lph_hold]) (by rw [upd_self, cph_hold, cph_hold, hc])
    (by rw [S.ph_set]; nofun) (by rw [upd_self, mph_hold mph_s W, mph_hold mph_s W, hm])
  rwa [upd_upd] at h

variable (mph_w : ∀ g a, M.ph (W.set g a) = M.ph g)
  (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g)
include mph_w hpl

/-- **The writer's take at the semaphore keeps the base** (`Fits.ofProduct`'s `utake`): the
count is not `0`, so the resource is posted and no thread is a reader (`cnt_idle`); the rwlock's
invariant by `Inv.take`. The client gives the laws of the places next to each other. -/
theorem utake {t : ThreadId} {g : γ} {h₁ h₂ r : Res} {sh sc} (hw : W.ph g = .ww)
    (hcnt : S.cnt (upd G t g) ≠ 0)
    (hu : W.Base Sz K (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m)
    (hS : S.Inv (upd G t (S.set (L.set (L.setPart (W.set g .wr) (rsum (L.part g) r)) .holds h₂)
      (.pst sh sc))) m)
    (hC : C.Inv L (upd G t (S.set (L.set (L.setPart (W.set g .wr) (rsum (L.part g) r)) .holds h₂)
      (.pst sh sc))) m) :
    W.Base Sz K (upd G t (S.set (L.set (L.setPart (W.set g .wr) (rsum (L.part g) r)) .holds h₂)
      (.pst sh sc))) rX m := by
  have hpp := place_lpart hpl (W.set g .wr) (rsum (L.part g) r)
  have hw₁ : W.ph (S.set (L.set g .holds h₁) (.pst sh sc)) = .ww := by rw [wph_hold, hw]
  have hpost : RwPosted W.ph (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) :=
    Classical.byContradiction fun hn => hcnt (by
      rw [cnt_congr (G := upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) (G' := upd G t g)
        (congrFun (upd_map W.ph G t (by rw [hw₁, hw]))), W.cnt_idle _ hn])
  have hwr : W.ph (S.set (L.set (L.setPart (W.set g .wr) (rsum (L.part g) r)) .holds h₂)
      (.pst sh sc)) = .wr := by
    rw [wph_hold]; exact (congrArg Prod.fst hpp).trans (W.ph_set _ _)
  have hm : M.ph (L.setPart (W.set g .wr) (rsum (L.part g) r)) = M.ph g := by
    rw [← W.pair.setPart, M.ph_setPart, mph_w]
  refine hu.handoverS mph_s lph ph_l
    (hu.winv.take hpost hw₁ hwr (by rw [mph_hold mph_s W, mph_hold mph_s W, hm])) hS hC
    (fun u => ?_) hm
    ((congrArg (fun p => p.2.1) hpp).trans (congrArg Prod.fst (W.sp_ph g .wr)))
  by_cases e : u = t
  · rw [e, upd_self, hwr]; rfl
  · have := hpost.2.1 u
    rwa [upd_ne _ _ e] at this ⊢

/-- **The last reader's give at the semaphore keeps the base** (`Fits.ofProduct`'s `upost`):
the rwlock's invariant by `Inv.post`, after which the resource is posted, so no thread is a
reader. -/
theorem upost {t : ThreadId} {g : γ} {h₁ h₂ r₀ : Res} {rc sh sc} (hw : W.ph g = .rp rc)
    (hu : W.Base Sz K (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m)
    (hS : S.Inv (upd G t (S.set (L.set (W.set (L.setPart g r₀) .out) .holds h₂) (.pst sh sc))) m)
    (hC : C.Inv L (upd G t (S.set (L.set (W.set (L.setPart g r₀) .out) .holds h₂) (.pst sh sc)))
      m) :
    W.Base Sz K (upd G t (S.set (L.set (W.set (L.setPart g r₀) .out) .holds h₂) (.pst sh sc)))
      rX m := by
  have hw₁ : (W.ph (S.set (L.set g .holds h₁) (.pst sh sc))).isRp = true := by
    rw [wph_hold, hw]; rfl
  have hout : W.ph (S.set (L.set (W.set (L.setPart g r₀) .out) .holds h₂) (.pst sh sc)) = .out := by
    rw [wph_hold, W.ph_set]
  have hm : M.ph (W.set (L.setPart g r₀) .out) = M.ph g := by
    rw [mph_w, ← W.pair.setPart, M.ph_setPart]
  obtain ⟨hI, hpost⟩ := hu.winv.post hw₁ hout (by rw [mph_hold mph_s W, mph_hold mph_s W, hm])
  exact hu.handoverS mph_s lph ph_l hI hS hC hpost.2.1 hm
    ((congrArg Prod.fst (W.sp_ph _ .out)).trans (congrArg (fun p => p.2.1) (place_lpart hpl g r₀)))

end

end Base

end FRw

end Full
end Zig
