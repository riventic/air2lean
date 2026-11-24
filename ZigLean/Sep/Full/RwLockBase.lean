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

The obligations of the builders, one theorem each: a stop (`Base.atStop`), a tick of a thread's
part in the outer mutex's view and in the semaphore's (`Base.tickM`, `Base.tickL`, from
`Base.tick`).
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

namespace Base

variable {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {rX : Res} {m : Mem}

/-- **A stop keeps the base** (`fitsM`'s and `fitsS`'s `atStop`): no part of it reads the current
thread. -/
theorem atStop (hu : W.Base Sz K G rX m) (t : ThreadId) :
    W.Base Sz K G rX { m with current := t } := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m.clocks[u]!) = true :=
    fun _ => VClock.le_refl _
  have hok := hu.winv.ok.fields_native (m' := { m with current := t }) rfl rfl rfl rfl hcl
  exact {
    winv := hu.winv.keep hok.1 hok.2 rfl rfl (fun _ => rfl) (fun _ => rfl) hu.winv.wm
      fun _ _ _ _ ho => ho
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
    pin := hu.pin }

/-- **A step of the outer mutex's code keeps the base** (`fitsM`'s `stable`): `t` runs it at a
calm place of the rwlock, out of the semaphore's code. The rwlock's invariant stays
(`Inv.otherStep`: `t` holds no writing bit at a calm place), the semaphore's primitive's rest
stays (`FSem.Sub.otherLock`), the window stays (the condition's writes stay, and every epoch write
still happened before the semaphore's mutex's holder), and the parts stay (`FLock.part_set`). The
outer mutex's place is none of the rwlock's or the semaphore's (`hpm`). -/
theorem stableM {t : ThreadId} {p : LPh} {h rL rH : Res} {m' : Mem} (hu : W.Base Sz K G rX m)
    (hM : M.Inv G (rsum (FLock.side L m rL rH) rX) m) (hk : L.Keeps G m rL rH rX)
    (hs : M.Step t m m') (hn : (M.ph (G t)).next p = true) (hcalm : W.prim.calm (W.place.ph (G t)))
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
  have hposted : RwPosted W.ph (upd G t (M.set (G t) p h)) ↔ RwPosted W.ph G := by
    simp only [RwPosted, hwph]
  have hpv : S.cnt (upd G t (M.set (G t) p h)) = S.cnt G := by
    by_cases hp : RwPosted W.ph G
    · rw [W.cnt_posted _ hp, W.cnt_posted _ (hposted.mpr hp)]
    · rw [W.cnt_idle _ hp, W.cnt_idle _ fun h => hp (hposted.mp h)]
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
    pin := hu.pin }

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
    pin := hu.pin }

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
  have hposted : RwPosted W.ph (upd G t (M.setPart (G t) r)) ↔ RwPosted W.ph G := by
    simp only [RwPosted, hwph]
  have hpv : S.cnt (upd G t (M.setPart (G t) r)) = S.cnt G := by
    by_cases hp : RwPosted W.ph G
    · rw [W.cnt_posted _ hp, W.cnt_posted _ (hposted.mpr hp)]
    · rw [W.cnt_idle _ hp, W.cnt_idle _ fun h => hp (hposted.mp h)]
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
    pin := hu.pin }

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

end Base

end FRw

end Full
end Zig
