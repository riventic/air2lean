import ZigLean.Sep.Full.RwLockImpl

/-!
# Why the outer mutex's view of `FRw.Fits` runs only at the calm places

`FRw.Fits.m` (`ZigLean/Sep/Full/RwLockImpl.lean`, module doc, "The outer mutex's code at the calm
places"; maintainer decision 2026-11-09, seventh RwLock obstruction, part (a), option A) is the
outer mutex `M`'s view with the rwlock as its primitive, where `ok` is the client's `okM` at the
semaphore's mutex's `away` and at a calm place of the primitive (`out`, `wi` or `rd`, out of the
semaphore's code).

1. `writer_release`: with the filter without the calm places (`okM ∧ L.away`, the form before the
   decision), the writer at `wr` holding `M` (the post of `lock_wp`), relabelled `away` from `L`
   (`laway`), is `ok`, so `FLock.Fits.stable` asks the view's `UM` after any release step of `M`
   from there (`MutexImpl.unlock`'s swap). `UM` keeps the rwlock's invariant (`prim.Sub`), whose
   `Inv.wm` (a writer holds `M`) is false after it. So no state of `P.inv` has a writer holding
   `M` where `M` admits a release step: `P.inv` holds at no post of `lock_wp`, and the writer's
   rules are vacuous. `okM` cannot exclude the step: `FRw.Fits.okM_set` makes it blind to the
   rwlock's place.
2. `wr_not_calm`: with the decided filter the writer at `wr` is at no calm place, so the view
   asks nothing of a step of `M`'s code there.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`. Run under
build-guard after the changed module build:
  lake env lean tests/roadmap/sync-contracts/RwLockFitsCX.lean
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Zig.Full.RwLockFitsCX

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C}
  {W : FRw γ X Y M L C S} {Tgt : Type} {P : Proto Tgt γ}
  {UM : (ThreadId → γ) → Res → Mem → Prop} {okM : γ → Prop}

/-- **The rejected filter is vacuous for writers**: the outer mutex's view at `okM ∧ L.away`
admits no state of `P.inv` with the writer at `wr` holding `M`, `away` from `L`, from which `M`
takes a release step (one of the code's transitions, `LPh.next`). -/
theorem writer_release (hm : M.Fits W.prim P UM (fun g => okM g ∧ L.ph g = .away))
    {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ} (hw : W.ph g = .wr)
    (hmh : M.ph g = .holds) (hl : L.ph g = .away) (hok : okM g) (hi : P.inv (upd G t g) m)
    (hstep : ∀ rX, M.Inv (upd G t g) rX m → ∃ m' p h, p.held = false ∧ (M.ph g).next p = true ∧
      M.Step t m m' ∧ (M.ph g = .holds → p ≠ .holds → M.Before m' (m.clocks[t]!)) ∧
      M.Transfer (upd G t g) rX m m' t p h) : False := by
  obtain ⟨rX, hM, hU⟩ := (hm.inv _ _).mp hi
  obtain ⟨m', p, h, hp, hn, hs, hb, htr⟩ := hstep rX hM
  have hU' := hm.stable _ rX m m' t p h (by rw [upd_self]; exact ⟨hok, hl⟩)
    (by rw [upd_self]; exact hn) (by rw [upd_self, hmh]; nofun) hM hU hs
    (by rw [upd_self]; exact hb) htr
  rw [upd_self] at hU'
  have hwph : W.ph (M.set g p h) = .wr := by
    rw [show W.ph (M.set g p h) = W.ph g from congrArg Prod.fst (hm.ph_l g p h), hw]
  have := (hm.sub _ _ _ hU').wm t (by rw [upd_self, hwph]; rfl)
  rw [upd_self, M.ph_set, hp] at this
  cases this

/-- **The decided filter excludes it**: the writer at `wr` is at no calm place of the rwlock's
primitive, so `FRw.Fits.m`'s `ok` is false there. -/
theorem wr_not_calm {g : γ} (hw : W.ph g = .wr) : ¬ W.prim.calm (W.place.ph g) := by
  rintro ⟨h | h | h, -⟩ <;> simp [FRw.place, hw, RwPh.isRd] at h

end Zig.Full.RwLockFitsCX

#print axioms Zig.Full.RwLockFitsCX.writer_release
#print axioms Zig.Full.RwLockFitsCX.wr_not_calm
