import Proofs.Sync.Cond
import ZigLean.Sep.Full.Sem

/-!
# `Io.Semaphore` of `examples/sync` as a semaphore (`SemImpl`)

The per-item obligation of `Io.Semaphore` (Zig 0.16.0's std code; 0.17.0's `waitUncancelable` and
`post` are the same code, and its `waitTimeout` is not covered) in this program's generated code:
`waitUncancelable` and `post` walked with the rules of a semaphore next to its mutex and condition
(`ZigLean/Sep/Full/Sem.lean`), with the program's `Io.Mutex` (`ioMutex`) and `Io.Condition`
(`ioCond`), for every protocol that has the semaphore, with any number of waiters and posters.
Both ops keep the caller's part (`keepPart`) and pay their ticks (the mutex's, the wait loop's,
the condition's) from its unmetered fragment (`payUnmetered`).
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto Zig.Full.FSem

namespace Sync

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Cond.lean`).
attribute [local irreducible] Proto.WP

variable {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `waitUncancelable` -/

/-- The wait loop's invariant: `t` holds the mutex in the semaphore's wait (`wt`). -/
def semWaitInv (P : Proto Tgt γ) (L : FLock γ) (S : FSem γ X L C) (t : ThreadId) (g : γ)
    (D : Nat) (_ : Io_Semaphore_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m

/-- The wait loop ends at a count other than 0. -/
def semWaitPost (P : Proto Tgt γ) (L : FLock γ) (S : FSem γ X L C) (t : ThreadId) (g : γ)
    (D : Nat)
    (r : Io_Semaphore_waitUncancelableExit × Io_Semaphore_waitUncancelableLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = .br4 ∧ d < D ∧ m.current = t ∧
    ∃ rL, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m ∧ S.cnt (upd G t g) ≠ 0

theorem semWaitLoop_body (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hwx : S.wx g)
    (hokg : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (hroom : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set (S.set g .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ n, (∀ u, n ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) n < 65535)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (D : Nat) (io : Io) (s : Io_Semaphore_waitUncancelableLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (h : semWaitInv P L S t g D s G m d) :
    P.WP t ((Io_Semaphore_waitUncancelable.loop5 S.p io).run s) (fun r G' m' d' =>
      if Io_Semaphore_waitUncancelable.again5 r.1 then semWaitInv P L S t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧
          (fun _ => 0) r.2 < (fun (_ : Io_Semaphore_waitUncancelableLocals) => 0) s)
      else semWaitPost P L S t g D r G' m' d') G m d := by
  have hF := hS.toFits
  obtain ⟨hd, hc, rL, hi⟩ := h
  unfold Io_Semaphore_waitUncancelable.loop5
  fsym [hF.wp_tick_unmetered, Fits.wp_cnt hF hcost, WP.liftMem_pure (projI hF _ _ _) rfl,
    wp_cwait ioCond hS hcost hLc S.ptr_c.symm S.ptr_l.symm t g hgx hwx hokg hu (fun _ h => h)
      hroom hlive,
    L.part_set, lpart_s hF, L.ph_set, S.cph_set, cph_l hF, pv_supd, pv_lupd,
    semWaitInv, semWaitPost, Io_Semaphore_waitUncancelable.again5]

/-- **`Io.Semaphore.waitUncancelable`** with the caller's part kept, at the caller's ghost value
(`SemImpl.wait_wp_resource` at the kept part). -/
theorem ioSem_wait_wp (hS : S.Fits P U ok) (hcost : P.cost = none) (hLc : L.c = ioMutex.c)
    {p : Ptr} (hp : p = S.p) (t : ThreadId) (g : γ) (gx : (ThreadId → X) → γ)
    (T : (ThreadId → X) → FAssn)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hwx : S.wx g) (hokg : ok g)
    (hxo : ∀ Y, L.ph (gx Y) = .out) (hxh : ∀ Y, L.held (gx Y) = rnil)
    (hxx : ∀ Y, C.ph (gx Y) = .out) (hxs : ∀ Y, S.ph (gx Y) = .out) (hokx : ∀ Y, ok (gx Y))
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → S.cnt (upd G t (gx (S.xs (upd G t g)))) = S.cnt (upd G t g) - 1)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → ∀ r, S.Pool (S.xs (upd G t g)) r →
      (S.Pool (S.xs (upd G t (gx (S.xs (upd G t g))))) ⋆ T (S.xs (upd G t g))) r)
    (hU : ∀ G rX m h₁ h₂ r sh sc, S.cnt (upd G t g) ≠ 0 → T (S.xs (upd G t g)) r →
      FHeap.Disjoint (L.part g).heap r.heap →
      U (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum (L.part g) r))
        .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum (L.part g) r))
        .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum (L.part g) r))
        .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum (L.part g) r))
        .holds h₂) (.pst sh sc))) rX m)
    (hroom : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set (S.set g .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ n, (∀ u, n ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) n < 65535)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m)
    (hc : m.current = t) :
    P.WP t (Io_Semaphore_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ Y r, T Y r ∧ FHeap.Disjoint (L.part g).heap r.heap ∧
        P.inv (upd G' t (L.setPart (gx Y) (rsum (L.part g) r))) m') G m d := by
  subst hp
  have hF := hS.toFits
  have hokp : ∀ Y r, ok (L.setPart (gx Y) r) := fun Y r => (hF.ok_setPart (gx Y) r).mpr (hokx Y)
  have hu' : ∀ r, 0 < (rsum (L.part g) r).gh.ac.frag .unmetered :=
    fun _ => Res.unmetered_rsum_left hu
  unfold Io_Semaphore_waitUncancelable
  fsym [WP.liftMem_pure (projI hF _ _ _) rfl,
    wp_lockWt ioMutex hF hcost S.ptr_l.symm hLc t g hgo hgx hgs hwx hokg hu,
    WP.loop _ _ (semWaitInv P L S t g d) (fun _ => 0) (semWaitPost P L S t g d)
      (semWaitLoop_body hS hcost hLc t g hgx hwx hokg hu hroom hlive d io),
    Fits.wp_cnt hF hcost, Fits.wp_take hF hcost hcnt hpool hU hgx hxx,
    wp_csignal ioCond hS hcost S.ptr_c.symm t,
    Fits.wp_unlockPst ioMutex hF hcost S.ptr_l.symm hLc t,
    ioMutex.unlock_wp_to hF hcost S.ptr_l.symm hLc t, hokp, hu',
    S.cph_set, S.ph_set, cph_l hF, cph_part hF, sph_l hF, sph_part hF, pv_lupd, pv_pupd,
    pv_supd, L.ph_set, L.ph_setPart, L.held_setPart, L.part_setPart, hxo, hxh, hxx, hxs,
    semWaitInv, semWaitPost]

/-- **`Io.Semaphore.waitUncancelable`** (`SemImpl.wait_wp_resource`): the kept part is the
caller's (`keepPart`), so the premises at it are at the caller's ghost value. -/
theorem ioSem_wait_wp_resource (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) {p : Ptr} (hp : p = S.p) (t : ThreadId) (g : γ)
    (gx : (ThreadId → X) → γ) (T : (ThreadId → X) → FAssn)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hwx : S.wx g) (hokg : ok g)
    (hxo : ∀ Y, L.ph (gx Y) = .out) (hxh : ∀ Y, L.held (gx Y) = rnil)
    (hxx : ∀ Y, C.ph (gx Y) = .out) (hxs : ∀ Y, S.ph (gx Y) = .out) (hokx : ∀ Y, ok (gx Y))
    (hcnt : ∀ rᵢ, keepPart t (L.part g) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (S.set (L.setPart g rᵢ) .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → S.cnt (upd G t (gx (S.xs (upd G t g)))) = S.cnt (upd G t g) - 1)
    (hpool : ∀ rᵢ, keepPart t (L.part g) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (S.set (L.setPart g rᵢ) .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → ∀ r, S.Pool (S.xs (upd G t g)) r →
      (S.Pool (S.xs (upd G t (gx (S.xs (upd G t g))))) ⋆ T (S.xs (upd G t g))) r)
    (hU : ∀ rᵢ, keepPart t (L.part g) rᵢ → ∀ G rX m h₁ h₂ r sh sc, S.cnt (upd G t g) ≠ 0 →
      T (S.xs (upd G t g)) r → FHeap.Disjoint rᵢ.heap r.heap →
      U (upd G t (S.set (L.set (L.setPart g rᵢ) .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum rᵢ r)) .holds h₂)
        (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum rᵢ r)) .holds h₂)
        (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum rᵢ r)) .holds h₂)
        (.pst sh sc))) m →
      U (upd G t (S.set (L.set (L.setPart (gx (S.xs (upd G t g))) (rsum rᵢ r)) .holds h₂)
        (.pst sh sc))) rX m)
    (hroom : ∀ rᵢ, keepPart t (L.part g) rᵢ → ∀ G₁ rL m₁,
      P.inv (upd G₁ t (L.set (S.set (L.setPart g rᵢ) .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ n, (∀ u, n ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) n < 65535)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Io_Semaphore_waitUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ Y r' r, keepPart t (L.part g) r' ∧ T Y r ∧ FHeap.Disjoint r'.heap r.heap ∧
        P.inv (upd G' t (L.setPart (gx Y) (rsum r' r))) m') G m d := by
  have hcnt := hcnt _ rfl
  have hpool := hpool _ rfl
  have hU := hU _ rfl
  have hroom := hroom _ rfl
  simp only [L.setPart_self] at hcnt hpool hU hroom
  refine WP.mono ?_ (ioSem_wait_wp hS hcost hLc hp t g gx T hgo hgx hgs hwx hokg hxo hxh hxx hxs
    hokx hcnt hpool hU hroom hlive io G m d hu hi hc)
  rintro _ G' m' d' ⟨hd, hc', Y, r, hT, hdj, hi'⟩
  exact ⟨hd, hc', Y, L.part g, r, rfl, hT, hdj, hi'⟩

/-! ## `post` -/

/-- **`Io.Semaphore.post`** with the kept part `L.part gx` exactly (`SemImpl.post_wp_resource` at
the kept part). -/
theorem ioSem_post_wp (hS : S.Fits P U ok) (hcost : P.cost = none) (hLc : L.c = ioMutex.c)
    {p : Ptr} (hp : p = S.p) (t : ThreadId) (g gx : γ) (rT : Res)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g)
    (hxo : L.ph gx = .out) (hxh : L.held gx = rnil) (hxx : C.ph gx = .out) (hxs : S.ph gx = .out)
    (hokx : ok gx)
    (hsplit : L.part g = rsum (L.part gx) rT) (hdj : FHeap.Disjoint (L.part gx).heap rT.heap)
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r)
    (hU : ∀ G rX m h₁ h₂ sh sc, U (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) rX m)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : 0 < (L.part gx).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m)
    (hc : m.current = t) :
    P.WP t (Io_Semaphore_post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t gx) m') G m d := by
  subst hp
  have hF := hS.toFits
  have hug : 0 < (L.part g).gh.ac.frag .unmetered := by
    rw [hsplit]; exact Res.unmetered_rsum_left hu
  unfold Io_Semaphore_post
  have hbound : ∀ {G rL m}, P.inv (upd G t (L.set g .holds rL)) m →
      (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64 := fun hi => (hcnt _ _ _ hi).2
  fsym [WP.liftMem_pure (projI hF _ _ _) rfl,
    ioMutex.lock_wp hF hcost S.ptr_l.symm hLc t g hgo hokg hug,
    Fits.wp_cnt hF hcost, hbound, Fits.wp_give hF hcost hcnt hpool hU hgx hgs hxx hsplit hdj,
    wp_csignal ioCond hS hcost S.ptr_c.symm t,
    ioMutex.unlock_wp_to hF hcost S.ptr_l.symm hLc t, hokx, hu,
    S.cph_set, S.ph_set, cph_l hF, sph_l hF, L.ph_set, hxo, hxh, hxx, hxs]

/-- **`Io.Semaphore.post`** (`SemImpl.post_wp_resource`): the kept part is `L.part gx`
(`keepPart`), so the premises at it are at the caller's ghost value. -/
theorem ioSem_post_wp_resource (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = ioMutex.c) {p : Ptr} (hp : p = S.p) (t : ThreadId) (g gx : γ) (rT : Res)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g)
    (hxo : L.ph gx = .out) (hxh : L.held gx = rnil) (hxx : C.ph gx = .out) (hxs : S.ph gx = .out)
    (hokx : ok gx)
    (hsplit : L.part g = rsum (L.part gx) rT) (hdj : FHeap.Disjoint (L.part gx).heap rT.heap)
    (hcnt : ∀ rᵢ, keepPart t (L.part gx) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (L.setPart g (rsum rᵢ rT)) .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64)
    (hpool : ∀ rᵢ, keepPart t (L.part gx) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (L.setPart g (rsum rᵢ rT)) .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r)
    (hU : ∀ rᵢ, keepPart t (L.part gx) rᵢ → ∀ G rX m h₁ h₂ sh sc,
      U (upd G t (S.set (L.set (L.setPart g (rsum rᵢ rT)) .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) rX m)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part gx)) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Io_Semaphore_post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r',
      keepPart t (L.part gx) r' ∧ P.inv (upd G' t (L.setPart gx r')) m') G m d := by
  have hg : L.setPart g (rsum (L.part gx) rT) = g := by rw [← hsplit, L.setPart_self]
  have hcnt := hcnt _ rfl
  have hpool := hpool _ rfl
  have hU := hU _ rfl
  simp only [hg, L.setPart_self] at hcnt hpool hU
  refine WP.mono ?_ (ioSem_post_wp hS hcost hLc hp t g gx rT hgo hgx hgs hokg hxo hxh hxx hxs hokx
    hsplit hdj hcnt hpool hU io G m d hu hi hc)
  rintro _ G' m' d' ⟨hd, hc', hi'⟩
  exact ⟨hd, hc', L.part gx, rfl, by rwa [L.setPart_self]⟩

/-- **`Io.Semaphore` of this program is a semaphore** (`SemImpl`), with the program's
`Io.Mutex` and `Io.Condition`: both ops keep the caller's part and pay from its unmetered
fragment. -/
def ioSem : SemImpl Tgt where
  wait := Io_Semaphore_waitUncancelable
  post := Io_Semaphore_post
  c := ioMutex.c
  wait_pre := payUnmetered
  wait_during := keepPart
  wait_post := keepPart
  wait_plain_pre _ _ := payUnmetered_plain
  wait_plain_during _ _ _ _ hr := hr
  wait_plain_post _ _ _ _ hr := hr
  post_pre := payUnmetered
  post_during := keepPart
  post_post := keepPart
  post_unmetered_pre _ _ hu := hu
  post_unmetered_during _ _ _ _ hr := hr
  post_unmetered_post _ _ _ _ hr := hr
  wait_wp_resource := ioSem_wait_wp_resource
  post_wp_resource := ioSem_post_wp_resource

end Sync
