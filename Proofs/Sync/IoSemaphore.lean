import Proofs.Sync.Cond
import ZigLean.Sep.Full.Sem

/-!
# `Io.Semaphore` of `examples/sync` as a semaphore (`SemImpl`)

The per-item obligation of `Io.Semaphore` (Zig 0.16.0's std code) in this program's generated
code: `waitUncancelable` and `post` walked with the rules of a semaphore next to its mutex and
condition (`ZigLean/Sep/Full/Sem.lean`), with the program's `Io.Mutex` (`ioMutex`) and
`Io.Condition` (`ioCond`), for every protocol that has the semaphore.
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto Zig.Full.FSem

namespace Sync

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Cond.lean`).
attribute [local irreducible] Proto.WP

variable {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `waitUncancelable` -/

/-- The wait loop's invariant: `t` holds the mutex at `g`'s other places. -/
def waitInv (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Io_Semaphore_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- The wait loop ends at a count other than 0. -/
def waitPost (P : Proto Tgt γ) (L : FLock γ) (S : FSem γ X L C) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Semaphore_waitUncancelableExit × Io_Semaphore_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = .br4 ∧ d < D ∧ m.current = t ∧
    ∃ rL, P.inv (upd G t (L.set g .holds rL)) m ∧ S.cnt (upd G t g) ≠ 0

theorem waitLoop_body (hS : L.Fits S.prim P U ok) (hcost : P.cost = none)
    (hok : ∀ g, ok g → S.ph g = .out) (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g) (hpl : (L.part g).Plain)
    (hone : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set g .holds rL)) m₁ → S.cnt (upd G₁ t g) = 0 →
      ∀ u, u ≠ t → ∀ i jr sn e, C.ph (G₁ u) ≠ .reg i jr sn e)
    (hlive : ∀ G₁ m₁, P.inv G₁ m₁ → (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (D : Nat) (io : Io) (s : Io_Semaphore_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (h : waitInv P L t g D s G m d) :
    P.WP t ((Io_Semaphore_waitUncancelable.loop5 S.p io).run s) (fun r G' m' d' =>
      if Io_Semaphore_waitUncancelable.again5 r.1 then waitInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧
          (fun _ => 0) r.2 < (fun (_ : Io_Semaphore_waitUncancelableLocals) => 0) s)
      else waitPost P L S t g D r G' m' d') G m d := by
  obtain ⟨hd, hc, rL, hi⟩ := h
  unfold Io_Semaphore_waitUncancelable.loop5
  fsym [Fits.wp_cnt hS hcost, WP.liftMem_pure (projI hS _ _ _) rfl,
    wp_cwait ioCond hS hcost hok hLc S.ptr_c.symm S.ptr_l.symm t g hgx hgs hokg hpl hone hlive,
    waitInv, waitPost, Io_Semaphore_waitUncancelable.again5]

/-- **`Io.Semaphore.waitUncancelable`** (`SemImpl.wait_wp`). -/
theorem ioSem_wait_wp (hS : L.Fits S.prim P U ok) (hcost : P.cost = none)
    (hok : ∀ g, ok g → S.ph g = .out) (hLc : L.c = ioMutex.c) {p : Ptr} (hp : p = S.p)
    (t : ThreadId) (g gx : γ) (T : FAssn)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g)
    (hpl : (L.part g).Plain)
    (hxo : L.ph gx = .out) (hxh : L.held gx = rnil) (hxx : C.ph gx = .out) (hxs : S.ph gx = .out)
    (hokx : ok gx)
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      S.cnt (upd G t gx) = S.cnt (upd G t g) - 1)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      ∀ r, S.Pool (S.xs (upd G t g)) r → (S.Pool (S.xs (upd G t gx)) ⋆ T) r)
    (hU : ∀ G rX m h₁ h₂ rp, U (upd G t (S.set (L.set g .holds h₁) .pst)) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx rp) .holds h₂) .pst)) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx rp) .holds h₂) .pst)) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx rp) .holds h₂) .pst)) m →
      U (upd G t (S.set (L.set (L.setPart gx rp) .holds h₂) .pst)) rX m)
    (hone : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set g .holds rL)) m₁ → S.cnt (upd G₁ t g) = 0 →
      ∀ u, u ≠ t → ∀ i jr sn e, C.ph (G₁ u) ≠ .reg i jr sn e)
    (hlive : ∀ G₁ m₁, P.inv G₁ m₁ → (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m)
    (hc : m.current = t) :
    P.WP t (Io_Semaphore_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r, T r ∧ FHeap.Disjoint (L.part g).heap r.heap ∧
        P.inv (upd G' t (L.setPart gx (rsum (L.part g) r))) m') G m d := by
  subst hp
  have hokp : ∀ r, ok (L.setPart gx r) := fun r => (hS.ok_setPart gx r).mpr hokx
  unfold Io_Semaphore_waitUncancelable
  fsym [WP.liftMem_pure (projI hS _ _ _) rfl,
    ioMutex.lock_wp hS hcost S.ptr_l.symm hLc t g hgo hokg,
    WP.loop _ _ (waitInv P L t g d) (fun _ => 0) (waitPost P L S t g d)
      (waitLoop_body hS hcost hok hLc t g hgx hgs hokg hpl hone hlive d io),
    Fits.wp_cnt hS hcost, Fits.wp_take hS hcost hcnt hpool hU hgx hgs hxx,
    wp_csignal ioCond hS hcost hok S.ptr_c.symm t,
    Fits.wp_unlockPst ioMutex hS hcost S.ptr_l.symm hLc t,
    wp_unlock ioMutex hS hcost S.ptr_l.symm hLc t, hokp,
    S.cph_set, S.ph_set, cph_l hS, cph_part hS, sph_l hS, sph_part hS, pv_lupd, pv_pupd,
    pv_supd, L.ph_set, L.ph_setPart, L.held_setPart, hxo, hxh, hxx, hxs, waitInv, waitPost]

/-! ## `post` -/

/-- **`Io.Semaphore.post`** (`SemImpl.post_wp`). -/
theorem ioSem_post_wp (hS : L.Fits S.prim P U ok) (hcost : P.cost = none)
    (hok : ∀ g, ok g → S.ph g = .out) (hLc : L.c = ioMutex.c) {p : Ptr} (hp : p = S.p)
    (t : ThreadId) (g gx : γ) (rT : Res)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g)
    (hxo : L.ph gx = .out) (hxh : L.held gx = rnil) (hxx : C.ph gx = .out) (hxs : S.ph gx = .out)
    (hokx : ok gx)
    (hsplit : L.part g = rsum (L.part gx) rT) (hdj : FHeap.Disjoint (L.part gx).heap rT.heap)
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r)
    (hU : ∀ G rX m h₁ h₂, U (upd G t (S.set (L.set g .holds h₁) .pst)) rX m →
      L.Inv (upd G t (S.set (L.set gx .holds h₂) .pst)) rX m →
      S.Inv (upd G t (S.set (L.set gx .holds h₂) .pst)) m →
      C.Inv L (upd G t (S.set (L.set gx .holds h₂) .pst)) m →
      U (upd G t (S.set (L.set gx .holds h₂) .pst)) rX m)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m)
    (hc : m.current = t) :
    P.WP t (Io_Semaphore_post p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t gx) m') G m d := by
  subst hp
  unfold Io_Semaphore_post
  have hbound : ∀ {G rL m}, P.inv (upd G t (L.set g .holds rL)) m →
      (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64 := fun hi => (hcnt _ _ _ hi).2
  fsym [WP.liftMem_pure (projI hS _ _ _) rfl,
    ioMutex.lock_wp hS hcost S.ptr_l.symm hLc t g hgo hokg,
    Fits.wp_cnt hS hcost, hbound, Fits.wp_give hS hcost hcnt hpool hU hgx hgs hxx hsplit hdj,
    wp_csignal ioCond hS hcost hok S.ptr_c.symm t,
    wp_unlock ioMutex hS hcost S.ptr_l.symm hLc t, hokx,
    S.cph_set, S.ph_set, cph_l hS, sph_l hS, L.ph_set, hxo, hxh, hxx, hxs]

/-- **`Io.Semaphore` of this program is a semaphore** (`SemImpl`), with the program's
`Io.Mutex` and `Io.Condition`. -/
def ioSem : SemImpl Tgt where
  wait := Io_Semaphore_waitUncancelable
  post := Io_Semaphore_post
  c := ioMutex.c
  wait_wp := ioSem_wait_wp
  post_wp := ioSem_post_wp

end Sync
