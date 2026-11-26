import ZigLean.Sep.Full.Sem
import ZigLean.Sep.Full.AutoWP

/-!
# `Io.Semaphore` as a semaphore (`SemImpl`), once for every program and Zig version

`Io.Semaphore`'s `waitUncancelable` and `post` (Zig 0.16.0 and 0.17.1; 0.17.1's `waitTimeout` is
not covered) are the same code in every program that uses them, up to names. `IoSemCode Tgt` is
that code passed as parameters, as `IoMutexCode` and `IoCondCode` are for `Io.Mutex` and
`Io.Condition`: a program's functions with their unfolding equations over the code's normal form
(`bind_assoc`, `pure_bind`, `ite_bind`), the generated matches on the code's own exits as
continuations of which the proof uses only their values at the exits it takes, and the mutex and
the condition the code calls as contract fields (`MutexImpl`, `CondImpl`; the condition's wait
admits and keeps a caller part with a positive unmetered fragment, `cwait_unm_pre`,
`cwait_unm_keep`).

`IoSemCode.impl` proves the semaphore contract (`SemImpl`, `ZigLean/Sep/Full/Sem.lean`) once, from
the rules of a semaphore next to its mutex and condition, for every protocol that has the
semaphore, with any number of waiters and posters. Both ops keep the caller's part (`keepPart`) and
pay their ticks (the mutex's, the wait loop's, the condition's) from its unmetered fragment
(`payUnmetered`). The straight-line parts (`lockLoopOf`, the loop body, `takeOf`, `postOf`'s
body) are `fsym` walks; the junctions at a continuation are rule steps (`WP.bind`, `WP.mono`, the
continuation's equation), since `fsym` cannot yet step through a continuation by its local
equation (ledger `fsym-abstract-shape`). A program instantiates it with its generated names and
`simp`/`rfl` proofs of the equations (`Proofs/Sync/IoSemaphore.lean`, and one instance per golden
case in `Proofs/Sync/SemCases.lean`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto FSem

namespace IoSemCode

variable {Tgt σ E : Type}

/-- `waitUncancelable`'s loop body, in normal form: the loop-entry tick, the count's load; at
count 0 the condition's wait (`wait`, at the condition `p + 12` with the mutex `p + 8`) and a
repeat, else the loop's end (`stop`). -/
def bodyOf (wait : Ptr → Io → Ptr → ConcM Tgt Unit) (rep stop : E) (p : Ptr) (io : Io) :
    CM Tgt σ E := do
  callMC tick
  let v ← Zig.load (BitVec 64) 8 p
  if v == (0 : BitVec 64) then do
    let pc ← callMC (ptrProject p (·.add 12))
    let pm ← callMC (ptrProject p (·.add 8))
    let _ ← callC (wait pc io pm)
    pure rep
  else pure stop

/-- `waitUncancelable` up to its loop's end, in normal form: the mutex's `lock` (at `p + 8`),
then the loop. -/
def lockLoopOf (lock : Ptr → Io → ConcM Tgt Unit) (body : Ptr → Io → CM Tgt σ E)
    (again : E → Bool) (p : Ptr) (io : Io) : CM Tgt σ E := do
  let pm ← callMC (ptrProject p (·.add 8))
  let _ ← callC (lock pm io)
  loop (body p io) again

/-- `waitUncancelable` in normal form: `lockLoopOf`, then `k`, the generated match after the loop;
`fin` is the one on the function's exit. -/
def waitOf [Inhabited σ] (lock : Ptr → Io → ConcM Tgt Unit) (body : Ptr → Io → CM Tgt σ E)
    (again : E → Bool) (k : Ptr → Io → E → CM Tgt σ E) (fin : E → ConcM Tgt Unit) (p : Ptr)
    (io : Io) : ConcM Tgt Unit := do
  let e ← StateT.run' (do
      let y ← lockLoopOf lock body again p io
      k p io y) default
  fin e

/-- The take after the wait loop, in normal form: the count's decrement; if permits are left, the
condition's `signal` (at `p + 12`); then the mutex's `unlock` (at `p + 8`). -/
def takeOf (signal unlock : Ptr → Io → ConcM Tgt Unit) (ret : E) (p : Ptr) (io : Io) :
    CM Tgt σ E := do
  let v ← Zig.load (BitVec 64) 8 p
  let w ← Zig.sub false v (1 : BitVec 64)
  Zig.store (α := BitVec 64) 8 p w
  let x ← Zig.load (BitVec 64) 8 p
  if Zig.gt false x (0 : BitVec 64) then do
    let pc ← callMC (ptrProject p (·.add 12))
    let _ ← callC (signal pc io)
    let pm ← callMC (ptrProject p (·.add 8))
    let _ ← callC (unlock pm io)
    pure ret
  else do
    let pm ← callMC (ptrProject p (·.add 8))
    let _ ← callC (unlock pm io)
    pure ret

/-- `post` in normal form: `lock`, the count's increment, `signal`, `unlock`; `fin` is the
generated match on the function's exit. -/
def postOf [Inhabited σ] (lock signal unlock : Ptr → Io → ConcM Tgt Unit) (ret : E)
    (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) : ConcM Tgt Unit := do
  let e ← StateT.run' ((do
      let pm ← callMC (ptrProject p (·.add 8))
      let _ ← callC (lock pm io)
      let v ← Zig.load (BitVec 64) 8 p
      let w ← Zig.add false v (1 : BitVec 64)
      Zig.store (α := BitVec 64) 8 p w
      let pc ← callMC (ptrProject p (·.add 12))
      let _ ← callC (signal pc io)
      let pm ← callMC (ptrProject p (·.add 8))
      let _ ← callC (unlock pm io)
      pure ret) : CM Tgt σ E) default
  fin e

end IoSemCode

/-- `Io.Semaphore`'s code in a program's generated code (module doc). -/
structure IoSemCode (Tgt : Type) where
  /-- The mutex and the condition the code calls, the condition's mutex being the mutex. -/
  M : MutexImpl Tgt
  C : CondImpl Tgt
  c_eq : C.c = M.c
  /-- The condition's wait admits a caller part with a positive unmetered fragment and keeps it. -/
  cwait_unm_pre : ∀ t r, 0 < r.gh.ac.frag .unmetered → C.wait_pre t r
  cwait_unm_keep : ∀ t r r', 0 < r.gh.ac.frag .unmetered → C.wait_post t r r' → r' = r
  /-- `waitUncancelable`'s locals and exits: the return, the loop's end, its repeat. -/
  σ : Type
  [inh : Inhabited σ]
  E : Type
  ret : E
  stop : E
  rep : E
  again : E → Bool
  again_rep : again rep = true := by rfl
  again_stop : again stop = false := by rfl
  /-- The wait loop's body. -/
  body : Ptr → Io → CM Tgt σ E
  body_eq : ∀ p io, body p io = IoSemCode.bodyOf C.wait rep stop p io
  /-- `waitUncancelable`. -/
  wait : Ptr → Io → ConcM Tgt Unit
  wait_eq : ∃ (k : Ptr → Io → E → CM Tgt σ E) (fin : E → ConcM Tgt Unit),
    (∀ p io, wait p io = IoSemCode.waitOf M.lock body again k fin p io) ∧
    (∀ p io, k p io stop = IoSemCode.takeOf C.signal M.unlock ret p io) ∧ fin ret = pure ()
  /-- `post`'s locals and exit. -/
  σp : Type
  [inhp : Inhabited σp]
  Ep : Type
  pret : Ep
  /-- `post`. -/
  post : Ptr → Io → ConcM Tgt Unit
  post_eq : ∃ fin : Ep → ConcM Tgt Unit,
    (∀ p io, post p io = IoSemCode.postOf (σ := σp) M.lock C.signal M.unlock pret fin p io) ∧
    fin pret = pure ()

namespace IoSemCode

attribute [instance] IoSemCode.inh IoSemCode.inhp

variable {Tgt : Type} (K : IoSemCode Tgt)

section
variable {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `waitUncancelable` -/

/-- The wait loop's invariant: `t` holds the mutex in the semaphore's wait (`wt`). -/
def waitInv (P : Proto Tgt γ) (L : FLock γ) (S : FSem γ X L C) (t : ThreadId) (g : γ)
    (D : Nat) (_ : K.σ) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m

/-- The wait loop ends at a count other than 0. -/
def waitPost (P : Proto Tgt γ) (L : FLock γ) (S : FSem γ X L C) (t : ThreadId) (g : γ)
    (D : Nat) (r : K.E × K.σ) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = K.stop ∧ d < D ∧ m.current = t ∧
    ∃ rL, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m ∧ S.cnt (upd G t g) ≠ 0

theorem loop_body (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = K.M.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hwx : S.wx g)
    (hokg : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (hroom : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set (S.set g .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ n, (∀ u, n ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) n < 65535)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (D : Nat) (io : Io) (s : K.σ) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (h : K.waitInv P L S t g D s G m d) :
    P.WP t ((K.body S.p io).run s) (fun r G' m' d' =>
      if K.again r.1 then K.waitInv P L S t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : K.σ) => 0) s)
      else K.waitPost P L S t g D r G' m' d') G m d := by
  have hF := hS.toFits
  obtain ⟨hd, hc, rL, hi⟩ := h
  rw [K.body_eq, bodyOf]
  fsym [hF.wp_tick_unmetered, Fits.wp_cnt hF hcost, WP.liftMem_pure (projI hF _ _ _) rfl,
    wp_cwait K.C hS hcost (hLc.trans K.c_eq.symm) S.ptr_c.symm S.ptr_l.symm t g hgx hwx hokg
      (K.cwait_unm_pre t _ hu) (fun r' => K.cwait_unm_keep t _ r' hu) hroom hlive,
    L.part_set, lpart_s hF, L.ph_set, S.cph_set, cph_l hF, pv_supd, pv_lupd,
    waitInv, waitPost, K.again_rep, K.again_stop]

/-- **`Io.Semaphore.waitUncancelable`** with the caller's part kept, at the caller's ghost value
(`SemImpl.wait_wp_resource` at the kept part). -/
theorem wait_wp (hS : S.Fits P U ok) (hcost : P.cost = none) (hLc : L.c = K.M.c)
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
    P.WP t (K.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ Y r, T Y r ∧ FHeap.Disjoint (L.part g).heap r.heap ∧
        P.inv (upd G' t (L.setPart (gx Y) (rsum (L.part g) r))) m') G m d := by
  subst hp
  have hF := hS.toFits
  have hokp : ∀ Y r, ok (L.setPart (gx Y) r) := fun Y r => (hF.ok_setPart (gx Y) r).mpr (hokx Y)
  have hu' : ∀ r, 0 < (rsum (L.part g) r).gh.ac.frag .unmetered :=
    fun _ => Res.unmetered_rsum_left hu
  obtain ⟨k, fin, hwait, hk, hfin⟩ := K.wait_eq
  rw [hwait, waitOf]
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  rw [StateT.run_bind]
  refine WP.bind (WP.mono (Q := K.waitPost P L S t g d) ?_ ?_)
  · -- the take, after the loop's end at a count other than 0 (`k` at `stop`)
    rintro ⟨y, s⟩ G₁ m₁ d₁ ⟨hy, hd₁, hc₁, rL, hi₁, hn₁⟩
    obtain rfl : y = K.stop := hy
    dsimp only
    rw [hk]
    refine WP.mono (Q := fun a G' m' d' => a.1 = K.ret ∧ d' < d ∧ m'.current = t ∧
      ∃ Y r, T Y r ∧ FHeap.Disjoint (L.part g).heap r.heap ∧
        P.inv (upd G' t (L.setPart (gx Y) (rsum (L.part g) r))) m') ?_ ?_
    · rintro ⟨e, s'⟩ G' m' d' ⟨he, h⟩
      obtain rfl : e = K.ret := he
      show P.WP t (fin K.ret) _ G' m' d'
      rw [hfin]
      exact WP.pure' h
    · rw [takeOf]
      fsym [WP.liftMem_pure (projI hF _ _ _) rfl,
        Fits.wp_cnt hF hcost, Fits.wp_take hF hcost hcnt hpool hU hgx hxx,
        wp_csignal K.C hS hcost S.ptr_c.symm t,
        Fits.wp_unlockPst K.M hF hcost S.ptr_l.symm hLc t,
        K.M.unlock_wp_to hF hcost S.ptr_l.symm hLc t, hokp, hu',
        S.cph_set, S.ph_set, cph_l hF, cph_part hF, sph_l hF, sph_part hF, pv_lupd, pv_pupd,
        pv_supd, L.ph_set, L.ph_setPart, L.held_setPart, L.part_setPart, hxo, hxh, hxx, hxs]
  · -- the lock and the loop
    rw [lockLoopOf]
    fsym [WP.liftMem_pure (projI hF _ _ _) rfl,
      wp_lockWt K.M hF hcost S.ptr_l.symm hLc t g hgo hgx hgs hwx hokg hu,
      WP.loop _ _ (K.waitInv P L S t g d) (fun _ => 0) (K.waitPost P L S t g d)
        (K.loop_body hS hcost hLc t g hgx hwx hokg hu hroom hlive d io),
      waitInv]

/-- **`Io.Semaphore.waitUncancelable`** (`SemImpl.wait_wp_resource`): the kept part is the
caller's (`keepPart`), so the premises at it are at the caller's ghost value. -/
theorem wait_wp_resource (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = K.M.c) {p : Ptr} (hp : p = S.p) (t : ThreadId) (g : γ)
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
    P.WP t (K.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ Y r' r, keepPart t (L.part g) r' ∧ T Y r ∧ FHeap.Disjoint r'.heap r.heap ∧
        P.inv (upd G' t (L.setPart (gx Y) (rsum r' r))) m') G m d := by
  have hcnt := hcnt _ rfl
  have hpool := hpool _ rfl
  have hU := hU _ rfl
  have hroom := hroom _ rfl
  simp only [L.setPart_self] at hcnt hpool hU hroom
  refine WP.mono ?_ (K.wait_wp hS hcost hLc hp t g gx T hgo hgx hgs hwx hokg hxo hxh hxx hxs
    hokx hcnt hpool hU hroom hlive io G m d hu hi hc)
  rintro _ G' m' d' ⟨hd, hc', Y, r, hT, hdj, hi'⟩
  exact ⟨hd, hc', Y, L.part g, r, rfl, hT, hdj, hi'⟩

/-! ## `post` -/

/-- **`Io.Semaphore.post`** with the kept part `L.part gx` exactly (`SemImpl.post_wp_resource` at
the kept part). -/
theorem post_wp (hS : S.Fits P U ok) (hcost : P.cost = none) (hLc : L.c = K.M.c)
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
    P.WP t (K.post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t gx) m') G m d := by
  subst hp
  have hF := hS.toFits
  have hug : 0 < (L.part g).gh.ac.frag .unmetered := by
    rw [hsplit]; exact Res.unmetered_rsum_left hu
  have hbound : ∀ {G rL m}, P.inv (upd G t (L.set g .holds rL)) m →
      (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64 := fun hi => (hcnt _ _ _ hi).2
  obtain ⟨fin, hpost, hfin⟩ := K.post_eq
  rw [hpost, postOf]
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map (WP.mono (Q := fun a G' m' d' => a.1 = K.pret ∧ d' < d ∧ m'.current = t ∧
    P.inv (upd G' t gx) m') ?_ ?_)
  · rintro ⟨e, s'⟩ G' m' d' ⟨he, h⟩
    obtain rfl : e = K.pret := he
    show P.WP t (fin K.pret) _ G' m' d'
    rw [hfin]
    exact WP.pure' h
  · fsym [WP.liftMem_pure (projI hF _ _ _) rfl,
      K.M.lock_wp hF hcost S.ptr_l.symm hLc t g hgo hokg trivial hug,
      Fits.wp_cnt hF hcost, hbound, Fits.wp_give hF hcost hcnt hpool hU hgx hgs hxx hsplit hdj,
      wp_csignal K.C hS hcost S.ptr_c.symm t,
      K.M.unlock_wp_to hF hcost S.ptr_l.symm hLc t, hokx, hu,
      S.cph_set, S.ph_set, cph_l hF, sph_l hF, L.ph_set, hxo, hxh, hxx, hxs]

/-- **`Io.Semaphore.post`** (`SemImpl.post_wp_resource`): the kept part is `L.part gx`
(`keepPart`), so the premises at it are at the caller's ghost value. -/
theorem post_wp_resource (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = K.M.c) {p : Ptr} (hp : p = S.p) (t : ThreadId) (g gx : γ) (rT : Res)
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
    P.WP t (K.post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r',
      keepPart t (L.part gx) r' ∧ P.inv (upd G' t (L.setPart gx r')) m') G m d := by
  have hg : L.setPart g (rsum (L.part gx) rT) = g := by rw [← hsplit, L.setPart_self]
  have hcnt := hcnt _ rfl
  have hpool := hpool _ rfl
  have hU := hU _ rfl
  simp only [hg, L.setPart_self] at hcnt hpool hU
  refine WP.mono ?_ (K.post_wp hS hcost hLc hp t g gx rT hgo hgx hgs hokg hxo hxh hxx hxs hokx
    hsplit hdj hcnt hpool hU io G m d hu hi hc)
  rintro _ G' m' d' ⟨hd, hc', hi'⟩
  exact ⟨hd, hc', L.part gx, rfl, by rwa [L.setPart_self]⟩

end

/-- **`Io.Semaphore` is a semaphore** (`SemImpl`), with its mutex and condition, in every program
and Zig version whose code it is: both ops keep the caller's part and pay from its unmetered
fragment. -/
def impl : SemImpl Tgt where
  wait := K.wait
  post := K.post
  c := K.M.c
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
  wait_wp_resource := K.wait_wp_resource
  post_wp_resource := K.post_wp_resource

end IoSemCode

end Full
end Zig
