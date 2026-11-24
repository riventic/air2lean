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
part at either lock (`Base.tick`).
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

/-- **A tick of `t`'s part keeps the base** (`FLock.Pair.TickKeeps` at either lock: the two locks
have one part, `FLock.Pair.setPart`): the tick changes no byte, so the rwlock's invariant stays
(`Inv.stepIn`; the rest's bytes are live, `FLock.Inv.rest_live`), the condition's and the
semaphore's stay (`FCond.Inv.other`, `FSem.Inv.outStep`), and the readers' shares are kept by
counting (`Shares.keep`), given the outer mutex's invariant before and after the tick at a rest
with the common rest (`s` is the other lock's side). The part is no place (`hpl`). -/
theorem tick {t : ThreadId} {r s : Res} (hu : W.Base Sz K G rX m) (hM : M.Inv G (rsum s rX) m)
    (hM' : M.Inv (upd G t (M.setPart (G t) r)) (rsum s rX) m.ticked) (hg : M.ph (G t) ≠ .gone)
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
    by_cases e : u = t
    · subst e; rw [upd_self, h]
    · rw [upd_ne _ _ e]
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
      (fun u q H l c hq hl => SCell.pos_add' _ (hu.winv.rest_share hq hl)) rfl
      (hM.w.live t hg).1 (fun u e => upd_ne _ _ e) (by rw [upd_self, wph])
    pin := hu.pin }

end Base

end FRw

end Full
end Zig
