import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.RwLockImpl

/-!
# `Io.RwLock` as a reader/writer lock (`RwLockImpl`), once for every program

`Io.RwLock`'s `lockUncancelable`, `unlock`, `lockSharedUncancelable` and `unlockShared` (Zig
0.16.0's std code; 0.17.0 translates to the same code) are the same code in every program that
uses them: only the names differ (each program's `Gen` defines its own exits and locals) and the
outer mutex and the semaphore they call are the program's `Io.Mutex` and `Io.Semaphore`.
`IoRwLockCode Tgt` is that code passed as parameters, built like `IoMutexCode`
(`ZigLean/Sep/Full/IoMutex.lean`): the functions of a program's `Gen` with their unfolding
equations over the code's normal form (`bind_assoc`, `pure_bind`), the generated matches on the
code's own exits as continuations of which the proof uses only their values at the exits it takes,
the outer mutex `M : MutexImpl` and the semaphore `S : SemImpl` the code calls, and the two
per-item facts of the semaphore's wait that the writer's wait needs (`FRw.wp_waitW`): it admits a
caller whose part has a positive unmetered fragment and keeps that part exactly (`wait_unm_pre`,
`wait_unm_keep`; for the program's `Io.Semaphore`, `payUnmetered` and `keepPart`).

`IoRwLockCode.impl` proves the reader/writer contract (`ZigLean/Sep/Full/RwLockImpl.lean`) once,
by walking each entry point with the contract's rules of the ops at the state word (`FRw.wp_addW`,
`wp_decW`, `wp_giveW`, `wp_loadW`, `wp_casR`, `wp_addR`, `wp_subR`), the writer's wait
(`FRw.wp_waitW`), the outer mutex's contract (`MutexImpl.lock_wp`, `unlock_wp`) and the
semaphore's (`SemImpl.post_wp_resource`, with the protocol's `upost`):

- `lock_wp`: `+2` (`wi`), the outer mutex, `-1`; with readers (the drain guard,
  `RwState.Family.drain_guard`) the writer waits at the semaphore for the resource.
- `unlock_wp`: `and ~1` (the resource back to the rest), then the outer mutex's unlock.
- `lockShared_wp`: a load, then the fast loop of weak CASes `+2^32` while the read value has no
  writer (each failure's value is `MsgOk`, so the checked add does not trap:
  `RwState.Family.checked_add_reader_stale`); a writer sends the reader the slow way, `+2^32`
  under the outer mutex. The reader's heap has `R` at the return's client parts (`FRw.Inv.rdR`).
- `unlockShared_wp`: `-2^32`; the last reader before a writer (`RwState.Family.last_guard`,
  `writing_guard`) posts the resource at the semaphore.

Each lock's code runs where the contract states its view (`FRw.Fits`, "Where each lock's code
runs"): the walks move the caller `out → away` at the semaphore's mutex around each call of the
outer mutex (`lock`'s and `unlock`'s, and `lockShared`'s slow path from before its lock until after
its unlock) and at the outer mutex around the last reader's post (`FRw.Fits.lAway`, `lUnaway`,
`mAway`, `mUnaway`); the two locks' `set`s commute (`FLock.Pair.set_comm`), so the relabel back
gives the exact ghost value (`FRw.Fits.lBack`, `FLock.Pair.set_around`). Each call of the outer
mutex is at a calm place of the rwlock (`FRw.Fits.okM_awaySet`, `okM_away`): `lock` at `wi`,
`unlock` at `out` after its `and ~1`, and `lockShared`'s slow path at `out` for the lock and at
`rd` for the unlock.

A program instantiates it with its names and `simp`/`rfl` proofs of the equations
(`Proofs/Sync/IoRwLock.lean`).

The walks are rule-by-rule term proofs, as `IoMutexCode`'s: `fsym` cannot yet walk a shape whose
continuations are hypotheses (ledger `fsym-abstract-shape`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace IoRwLockCode

variable {Tgt σ E : Type} [Inhabited σ]

/-- `lockUncancelable` in normal form: `+2`, the outer mutex, `-1`, and the semaphore's wait if the
old value has readers. `kW` is the generated match after the drain branch, `fin` the one on the
function's exit. -/
def lockOf (M : MutexImpl Tgt) (S : SemImpl Tgt) (mid : E) (kW : E → CM Tgt σ E)
    (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) : ConcM Tgt Unit := do
  let e ← StateT.run' ((do
      let _ ← atomicRmwC .add false .seqCst 8 p (2 : BitVec 64)
      let pm ← callMC (ptrProject p (·.add 32))
      let _ ← callC (M.lock pm io)
      let old ← atomicRmwC .add false .seqCst 8 p (18446744073709551615 : BitVec 64)
      let x ← (if (old &&& (9223372032559808512 : BitVec 64) != (0 : BitVec 64)) then (do
          let ps ← callMC (ptrProject p (·.add 8))
          let _ ← callC (S.wait ps io)
          pure mid)
        else pure mid)
      kW x) : CM Tgt σ E) default
  fin e

/-- `unlock` in normal form: `and ~1`, then the outer mutex's unlock. -/
def unlockOf (M : MutexImpl Tgt) (ret : E) (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) :
    ConcM Tgt Unit := do
  let e ← StateT.run' ((do
      let _ ← atomicRmwC .and false .seqCst 8 p (18446744073709551614 : BitVec 64)
      let pm ← callMC (ptrProject p (·.add 32))
      let _ ← callC (M.unlock pm io)
      pure ret) : CM Tgt σ E) default
  fin e

/-- `lockSharedUncancelable`'s loop body in normal form: the loop-entry tick; while the local
`state` has no writer, the checked add of a reader (`addR`: `Zig.add false · 2^32` in the code,
`IoRwLockCode.body_eq`) and the weak CAS (`k15` the generated match on its exit: a failure stores
the value read and repeats); `kB` the match on the body's exit. -/
def bodyOf (getSt : σ → BitVec 64) (addR : BitVec 64 → Result (BitVec 64))
    (k15 kB : E → CM Tgt σ E) (fail : BitVec 64 → E) (ret slow : E) (p : Ptr) : CM Tgt σ E := do
  callMC tick
  let s ← get
  let y ← (if (getSt s &&& (4294967295 : BitVec 64) == (0 : BitVec 64)) then (do
      let s₁ ← get
      let s₂ ← get
      let n ← addR (getSt s₂)
      let r ← cmpxchgWeakC .seqCst .seqCst 8 p (getSt s₁) n
      let z ← (if r.isSome then (do
          let v ← Zig.optPayload r
          pure (fail v))
        else pure ret)
      k15 z)
    else pure slow)
  kB y

/-- `lockSharedUncancelable`'s slow path in normal form: `+2^32` under the outer mutex. -/
def slowOf (M : MutexImpl Tgt) (ret : E) (p : Ptr) (io : Io) : CM Tgt σ E := do
  let pm ← callMC (ptrProject p (·.add 32))
  let _ ← callC (M.lock pm io)
  let _ ← atomicRmwC .add false .seqCst 8 p (4294967296 : BitVec 64)
  let pm' ← callMC (ptrProject p (·.add 32))
  let _ ← callC (M.unlock pm' io)
  pure ret

/-- `lockSharedUncancelable` in normal form: the load into the local `state`, the loop, and the
generated match on the loop's exit (`kS`: the slow path at its exit) and on the function's. -/
def lockSharedOf (setSt : σ → BitVec 64 → σ) (body : Ptr → CM Tgt σ E) (again : E → Bool)
    (kS : Ptr → Io → E → CM Tgt σ E) (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) :
    ConcM Tgt Unit := do
  let e ← StateT.run' ((do
      let v ← atomicLoadC (n := 64) .seqCst 8 p
      modify (fun s => setSt s v)
      let y ← loop (body p) again
      kS p io y) : CM Tgt σ E) default
  fin e

/-- `unlockShared` in normal form: `-2^32`, the last-reader guard and the writing bit (`k8` the
exit carrying it), the generated match that posts at the semaphore (`k1`), and the matches on its
exit (`k2`) and on the function's (`fin`). -/
def unlockSharedOf (k8 : Bool → E) (k1 : Ptr → Io → E → CM Tgt σ E) (k2 : E → CM Tgt σ E)
    (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) : ConcM Tgt Unit := do
  let e ← StateT.run' ((do
      let old ← atomicRmwC .sub false .seqCst 8 p (4294967296 : BitVec 64)
      let x ← (if (old &&& (9223372032559808512 : BitVec 64) == (4294967296 : BitVec 64)) then
          pure (k8 (old &&& (1 : BitVec 64) != (0 : BitVec 64)))
        else pure (k8 false))
      let y ← k1 p io x
      k2 y) : CM Tgt σ E) default
  fin e

end IoRwLockCode

/-- `Io.RwLock`'s code in a program's generated code (module doc). -/
structure IoRwLockCode (Tgt : Type) where
  /-- The outer mutex and the semaphore the code calls, with one contended value. -/
  M : MutexImpl Tgt
  S : SemImpl Tgt
  c_eq : S.c = M.c
  /-- The semaphore's wait admits a positive unmetered fragment and keeps that part. -/
  wait_unm_pre : ∀ t r, 0 < r.gh.ac.frag .unmetered → S.wait_pre t r
  wait_unm_keep : ∀ t r r', 0 < r.gh.ac.frag .unmetered →
    (S.wait_during t r r' → r' = r) ∧ (S.wait_post t r r' → r' = r)
  /-- `lockUncancelable`'s locals and exits (the return, the end of the drain branch). -/
  σL : Type
  [inhL : Inhabited σL]
  EL : Type
  lret : EL
  lmid : EL
  lock : Ptr → Io → ConcM Tgt Unit
  lock_eq : ∃ (kW : EL → CM Tgt σL EL) (fin : EL → ConcM Tgt Unit),
    (∀ p io, lock p io = IoRwLockCode.lockOf M S lmid kW fin p io) ∧
    kW lmid = pure lret ∧ fin lret = pure ()
  /-- `unlock`'s locals and exit. -/
  σU : Type
  [inhU : Inhabited σU]
  EU : Type
  uret : EU
  unlock : Ptr → Io → ConcM Tgt Unit
  unlock_eq : ∃ fin : EU → ConcM Tgt Unit,
    (∀ p io, unlock p io = IoRwLockCode.unlockOf (σ := σU) M uret fin p io) ∧ fin uret = pure ()
  /-- `lockSharedUncancelable`'s locals (the local `state`) and exits: the return, the slow path,
  the CAS's failure with the value read, the body's end before a repeat, the repeat. -/
  σR : Type
  [inhR : Inhabited σR]
  ER : Type
  getSt : σR → BitVec 64
  setSt : σR → BitVec 64 → σR
  get_set : ∀ s v, getSt (setSt s v) = v
  rret : ER
  rslow : ER
  rfail : BitVec 64 → ER
  rnext : ER
  rrep : ER
  again : ER → Bool
  again_rep : again rrep = true
  again_ret : again rret = false
  again_slow : again rslow = false
  body : Ptr → CM Tgt σR ER
  body_eq : ∃ (k15 kB : ER → CM Tgt σR ER),
    (∀ p, body p = IoRwLockCode.bodyOf getSt (Zig.add false · (4294967296 : BitVec 64)) k15 kB
      rfail rret rslow p) ∧
    (∀ v, k15 (rfail v) = do modify (fun s => setSt s v); pure rnext) ∧
    k15 rret = pure rret ∧ kB rnext = pure rrep ∧ kB rret = pure rret ∧ kB rslow = pure rslow
  lockShared : Ptr → Io → ConcM Tgt Unit
  lockShared_eq : ∃ (kS : Ptr → Io → ER → CM Tgt σR ER) (fin : ER → ConcM Tgt Unit),
    (∀ p io, lockShared p io = IoRwLockCode.lockSharedOf setSt body again kS fin p io) ∧
    (∀ p io, kS p io rslow = IoRwLockCode.slowOf M rret p io) ∧
    (∀ p io, kS p io rret = pure rret) ∧ fin rret = pure ()
  /-- `unlockShared`'s locals and exits: the return, the end of the post branch, the exit with the
  writing bit. -/
  σS : Type
  [inhS : Inhabited σS]
  ES : Type
  sret : ES
  smid : ES
  s8 : Bool → ES
  unlockShared : Ptr → Io → ConcM Tgt Unit
  unlockShared_eq : ∃ (k1 : Ptr → Io → ES → CM Tgt σS ES) (k2 : ES → CM Tgt σS ES)
      (fin : ES → ConcM Tgt Unit),
    (∀ p io, unlockShared p io = IoRwLockCode.unlockSharedOf s8 k1 k2 fin p io) ∧
    (∀ p io, k1 p io (s8 true) = do
      let ps ← callMC (ptrProject p (·.add 8))
      let _ ← callC (S.post ps io)
      pure smid) ∧
    (∀ p io, k1 p io (s8 false) = pure smid) ∧ k2 smid = pure sret ∧ fin sret = pure ()

namespace IoRwLockCode

attribute [instance] IoRwLockCode.inhL IoRwLockCode.inhU IoRwLockCode.inhR IoRwLockCode.inhS

/-- **The frame of an entry point**: its locals' run from `default`, then the generated match on
its exit, which is `pure ()` at the return. -/
theorem wp_frame {Tgt σ E γ : Type} [Inhabited σ] {P : Proto Tgt γ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem}
    {n : Nat} {x : CM Tgt σ E} {fin : E → ConcM Tgt Unit} {ret : E} (hfin : fin ret = pure ())
    {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t (x.run default) (fun r G' m' d' => r.1 = ret ∧ Q () G' m' d') G m n) :
    P.WP t (do let e ← x.run' default; fin e) Q G m n := by
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map (WP.mono ?_ h)
  rintro r G' m' d' ⟨he, hq⟩
  show P.WP t (fin r.1) Q G' m' d'
  rw [he, hfin]
  exact WP.pure' hq

variable (C : IoRwLockCode Tgt) {γ X Y : Type} {M L : FLock γ} {Cn : FCond γ}
  {S : FSem γ Y L Cn} {W : FRw γ X Y M L Cn S} {P : Proto Tgt γ}
  {UM US : (ThreadId → γ) → Res → Mem → Prop} {okM okS : γ → Prop}

/-! ## `lockUncancelable` -/

/-- **`lockUncancelable`** (`RwLockImpl.lock_wp`): `+2`, the outer mutex, `-1`; with readers the
writer waits at the semaphore (`FRw.wp_waitW`), else it takes the free resource at the `-1`. -/
theorem lock_wp (hW : W.Fits P UM US okM okS) (hcost : P.cost = none) (hMc : M.c = C.M.c)
    (hLc : L.c = C.M.c) {p : Ptr} (hp : p = W.p) (t : ThreadId) (g : γ) (hg : W.Out g)
    (hokM : okM g) (hokS : okS g) (hu : 0 < (M.part g).gh.ac.frag .unmetered)
    (hroom : ∀ G m, P.inv G m → W.ph (G t) = .out → W.nwi G m + 1 < RwState.countBound)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m)
    (_hc : m.current = t) :
    P.WP t (C.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r rM, (∃ G₀, W.R (W.xs (upd G₀ t g)) r) ∧ FHeap.Disjoint (M.part g).heap r.heap ∧
        P.inv (upd G' t (M.set (W.set (M.setPart g (rsum (M.part g) r)) .wr) .holds rM)) m')
      G m d := by
  obtain ⟨hwo, hmo, -, hlo, hlh, hco, hso⟩ := hg
  have hsc := FRw.splace_out hco hso
  obtain rfl : p = W.st.ptr := hp.trans W.ptr_st.symm
  obtain ⟨kW, fin, hlock, hkW, hfin⟩ := C.lock_eq
  rw [hlock, lockOf]
  refine wp_frame hfin ?_
  rw [StateT.run_bind]
  refine WP.bind (FRw.wp_addW hW hwo (by rw [hmo]; decide) hsc hroom hi
    fun k₁ hk₁ G₁ m₁ _ hc₁ hi₁ => ?_)
  rw [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (hW.projW hi₁ (by decide) (by decide)) ?_)
  -- the outer mutex's lock runs `away` from the semaphore's mutex (`Fits.lAway`, `lUnaway`)
  have hlx : L.ph (W.set g .wi) = .out := by rw [W.lph, hlo]
  have hmx : M.ph (W.set g .wi) = .out := by rw [hW.mph, hmo]
  rw [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono (fun _ G₂ m₂ k₂ h₂ => ?_)
    (C.M.lock_wp hW.m hcost (by rw [W.ptr_m, ← W.ptr_st]) hMc t (L.set (W.set g .wi) .away rnil)
      (by rw [W.pair.ph_ba, hmx]) (hW.okM_awaySet hokM (.inr (.inl rfl)) hsc)
      (by rw [W.pair.part_ba, hW.mpart]; exact hu)
      io G₁ m₁ k₁ (hW.lAway hlx (.inl hmx) hi₁))))
  obtain ⟨hk₂, hc₂, rL, hi₂⟩ := h₂
  replace hi₂ := hW.lBack hlx (by rw [W.lheld, hlh]) (.inr rfl) hi₂
  -- `t` holds the outer mutex at `wi`
  have hpart₂ : M.part (M.set (W.set g .wi) .holds rL) = M.part g := by
    rw [M.part_set, hW.mpart]
  have hx₂ : ∀ G₀, W.xs (upd G₀ t (M.set (W.set g .wi) .holds rL)) = W.xs (upd G₀ t g) :=
    fun G₀ => upd_map W.x G₀ t (by rw [W.x_m, W.x_set])
  have hset₂ : ∀ X, W.set (M.setPart (M.set (W.set g .wi) .holds rL) X) .wr =
      M.set (W.set (M.setPart g X) .wr) .holds rL := fun X => by
    rw [M.setPart_set, ← hW.wset_part, hW.wset_m, W.set_set]
  rw [StateT.run_bind]
  refine WP.bind (FRw.wp_decW hW (g := M.set (W.set g .wi) .holds rL)
    (by rw [(hW.ph_m _ _ _).1, W.ph_set]) (M.ph_set _ _ _)
    (by rw [hW.splace_m, W.sp_ph]; exact hsc) hi₂
    fun k₃ hk₃ G₃ m₃ old hc₃ hcase => ?_)
  have hgo : (old &&& (9223372032559808512 : BitVec 64) != (0 : BitVec 64)) =
      (RwState.readers old != 0) := RwState.Family.drain_guard 31 1 old
  rw [StateT.run_bind]
  refine WP.bind ?_
  split
  · rename_i hcd
    rcases hcase with ⟨-, hi₃⟩ | ⟨hro, -⟩
    · -- readers drain: the writer waits at the semaphore for the resource
      rw [StateT.run_bind]
      refine WP.bind (WP.callMC_ptrProject (hW.projW hi₃ (by decide) (by decide)) ?_)
      rw [StateT.run_bind]
      refine WP.bind (WP.callC (WP.mono (fun _ G₄ m₄ k₄ h₄ => ?_)
        (FRw.wp_waitW hW hcost C.S (hLc.trans C.c_eq.symm) C.wait_unm_pre C.wait_unm_keep
          (by rw [W.ptr_s, ← W.ptr_st]) (W.ph_set _ _) (by rw [hW.mph, M.ph_set])
          (by rw [W.lph, W.pair.ph_ab, W.lph, hlo])
          (by rw [W.lheld, W.pair.held_ab, W.lheld, hlh])
          (by rw [FRw.cph_w, (hW.ph_m _ _ _).2.1, FRw.cph_w, hco])
          (by rw [FRw.sph_w, (hW.ph_m _ _ _).2.2, FRw.sph_w, hso])
          ((hW.okS_set _ _).mpr ((hW.okS_m _ _ _).mpr ((hW.okS_set _ _).mpr hokS)))
          (by rw [hW.mpart, hpart₂]; exact hu) io hi₃ hc₃)))
      obtain ⟨hk₄, hc₄, r, ⟨G₀, hR⟩, hdj, hi₄⟩ := h₄
      rw [hW.mpart, hpart₂] at hdj hi₄
      rw [← hW.wset_part, W.set_set, hset₂] at hi₄
      rw [FRw.xs_set, hx₂] at hR
      rw [StateT.run_pure]
      refine WP.pure' ?_
      simp only [hkW, StateT.run_pure]
      exact WP.pure' ⟨rfl, by omega, hc₄, r, rL, ⟨G₀, hR⟩, hdj, hi₄⟩
    · rw [hgo, hro] at hcd
      exact absurd hcd (by decide)
  · rename_i hcd
    rcases hcase with ⟨hro, -⟩ | ⟨-, r, hR, hdj, hi₃⟩
    · exact absurd (by rw [hgo]; simpa using hro) hcd
    · -- no reader: `t` took the free resource at the `-1`
      rw [hpart₂] at hdj hi₃
      rw [hset₂] at hi₃
      rw [hx₂] at hR
      rw [StateT.run_pure]
      refine WP.pure' ?_
      simp only [hkW, StateT.run_pure]
      exact WP.pure' ⟨rfl, by omega, hc₃, r, rL, ⟨G₃, hR⟩, hdj, hi₃⟩

/-! ## `unlock` -/

/-- **`unlock`** (`RwLockImpl.unlock_wp`): `and ~1` gives the resource back to the rest
(`FRw.wp_giveW`), then the outer mutex's unlock. -/
theorem unlock_wp (hW : W.Fits P UM US okM okS) (hcost : P.cost = none) (hMc : M.c = C.M.c)
    (_hLc : L.c = C.M.c) {p : Ptr} (hp : p = W.p) (t : ThreadId) (g : γ) (r₀ r : Res)
    (hwr : W.ph g = .wr) (hmh : M.ph g = .holds) (hlo : L.ph g = .out) (hlh : L.held g = rnil)
    (hco : Cn.ph g = .out) (hso : S.ph g = .out) (hpart : M.part g = rsum r₀ r)
    (hd : FHeap.Disjoint r₀.heap r.heap) (hokM : okM g) (_hokS : okS g)
    (_hu : 0 < r₀.gh.ac.frag .unmetered) (hR : ∀ G, W.R (W.xs (upd G t g)) r)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m)
    (_hc : m.current = t) :
    P.WP t (C.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (M.set (W.set (M.setPart g r₀) .out) .out rnil)) m') G m d := by
  obtain rfl : p = W.st.ptr := hp.trans W.ptr_st.symm
  obtain ⟨fin, hunlock, hfin⟩ := C.unlock_eq
  rw [hunlock, unlockOf]
  refine wp_frame hfin ?_
  rw [StateT.run_bind]
  have hsc := FRw.splace_out hco hso
  refine WP.bind (FRw.wp_giveW hW hwr (by rw [hmh]; decide) hpart hd hR hsc hi
    fun k₁ hk₁ G₁ m₁ _ hc₁ hi₁ => ?_)
  rw [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (hW.projW hi₁ (by decide) (by decide)) ?_)
  -- the outer mutex's unlock runs `away` from the semaphore's mutex (`Fits.lAway`, `lUnaway`)
  have hlx : L.ph (W.set (M.setPart g r₀) .out) = .out := by
    rw [W.lph, W.pair.setPart, L.ph_setPart, hlo]
  have hmx : M.ph (W.set (M.setPart g r₀) .out) = .holds := by rw [hW.mph, M.ph_setPart, hmh]
  rw [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono (fun _ G₂ m₂ k₂ h₂ => ?_)
    (C.M.unlock_wp hW.m hcost (by rw [W.ptr_m, ← W.ptr_st]) hMc t
      (L.set (W.set (M.setPart g r₀) .out) .away rnil) (by rw [W.pair.ph_ba, hmx])
      (hW.okM_awaySet ((hW.okM_part _ _ hsc).mpr hokM) (.inl rfl)
        (by rw [hW.splace_part]; exact hsc))
      io G₁ m₁ k₁ (hW.lAway hlx (.inr hmx) hi₁) hc₁)))
  obtain ⟨hk₂, hc₂, hi₂⟩ := h₂
  replace hi₂ :=
    hW.lBack hlx (by rw [W.lheld, W.pair.setPart, L.held_setPart, hlh]) (.inl rfl) hi₂
  rw [StateT.run_pure]
  exact WP.pure' ⟨rfl, by omega, hc₂, hi₂⟩

/-! ## `lockSharedUncancelable` -/

/-- The fast loop's invariant: `t` is `out` and the local `state` holds a value of the word
(`MsgOk`). -/
def lsInv (P : Proto Tgt γ) (t : ThreadId) (g : γ) (D : Nat)
    (s : C.σR) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ FRw.MsgOk (C.getSt s) ∧ P.inv (upd G t g) m

/-- The fast loop ends at the return with the reader's share in `t`'s part, or at the slow
path with `t` still `out`. -/
def lsPost (P : Proto Tgt γ) (W : FRw γ X Y M L Cn S) (t : ThreadId) (g : γ) (D : Nat)
    (r : C.ER × C.σR) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
    ((r.1 = C.rret ∧ ∃ (q : Frac) (H : FHeap), 0 < q.val ∧
      P.inv (upd G t (W.set (M.setPart g (rsum (M.part g) (shareRes H q))) (.rd q H))) m) ∨
     (r.1 = C.rslow ∧ P.inv (upd G t g) m))

/-- One run of the fast loop's body: the tick; with no writer in `state`, the checked add and the
weak CAS (`FRw.wp_casR`): its success ends the loop with the share, its failure stores the value
read (`MsgOk`) and repeats (a stop: the depth gets smaller). -/
theorem body_wp (hW : W.Fits P UM US okM okS) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hout : W.ph g = .out) (hmg : M.ph g ≠ .gone) (hsc : S.place.ph g = (.out, .out))
    (hu : 0 < (M.part g).gh.ac.frag .unmetered)
    (hroom : ∀ G m, P.inv G m → W.ph (G t) = .out → W.nrd G m + 1 < RwState.countBound)
    (D : Nat) (s : C.σR) (G : ThreadId → γ) (m : Mem) (d : Nat) (h : C.lsInv P t g D s G m d) :
    P.WP t ((C.body W.st.ptr).run s) (fun r G' m' d' =>
      if C.again r.1 then C.lsInv P t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : C.σR) => 0) s)
      else C.lsPost P W t g D r G' m' d') G m d := by
  obtain ⟨hD, hc, ⟨rr, ww, aa, hrr, hww, hst⟩, hi⟩ := h
  obtain ⟨k15, kB, hbody, hk15f, hk15r, hkB9, hkBr, hkB7⟩ := C.body_eq
  -- the checked add, abstracted: its overflow test of the unknown `state` against `2^64` unfolds
  -- unary on the literal, so the walk keeps it a variable and uses only its value at `MsgOk`
  -- (ledger `fsym-abstract-shape`)
  have haddR : ∀ r w a, r < RwState.countBound → w < RwState.countBound →
      (Zig.add false · (4294967296 : BitVec 64)) (RwState.encode r w a) =
        pure (RwState.encode (r + 1) w a) := fun r w a hr hw =>
    RwState.Family.checked_add_reader_stale (by decide) hr hw a true
  rw [hbody]
  generalize (Zig.add false · (4294967296 : BitVec 64)) = addR at haddR ⊢
  rw [bodyOf, StateT.run_bind]
  refine WP.bind ?_
  rw [CNorm.run_callMC]
  refine WP.bind (hW.m.wp_tick_unmetered hi hc hmg hu fun m₀ hc₀ hi₀ => WP.pure' ?_)
  -- `rw`, not `simp`: `simp`'s `rfl` steps over the body leave the kernel a defeq check that
  -- times out (ledger `fsym-abstract-shape`)
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind]
  refine WP.bind ?_
  by_cases hgd : (C.getSt s &&& (4294967295 : BitVec 64) == (0 : BitVec 64)) = true
  · rw [ite_eq_left hgd, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind,
      StateT.run_get, pure_bind, StateT.run_bind, CNorm.run_liftR, ← CNorm.run_callRC]
    refine WP.bind (WP.callRC_ok (v := RwState.encode (rr + 1) ww aa)
      (by rw [hst, haddR rr ww aa hrr hww]; rfl) ?_)
    rw [StateT.run_bind]
    refine WP.bind (FRw.wp_casR hW hout hmg hsc hroom (beq_iff_eq.mp hgd)
      (by rw [hst]; exact (RwState.Family.add_reader 31 1 rr ww aa).symm) hi₀
      (fun k hk G₁ m₁ hc₁ q H hq _ hi₁ => ?_) (fun k hk G₁ m₁ b hc₁ hb hi₁ => ?_))
    · -- success: the reader is in
      rw [StateT.run_bind, CNorm.run_ite,
        ite_eq_right (show ¬(none : Option (BitVec 64)).isSome = true from Bool.false_ne_true),
        StateT.run_pure, pure_bind, hk15r, StateT.run_pure]
      refine WP.pure' ?_
      rw [hkBr, StateT.run_pure]
      refine WP.pure' ?_
      rw [C.again_ret, ite_eq_right Bool.false_ne_true]
      exact ⟨by omega, hc₁, .inl ⟨rfl, q, H, hq, hi₁⟩⟩
    · -- failure: store the value read and repeat
      rw [StateT.run_bind, CNorm.run_ite,
        ite_eq_left (show (some b).isSome = true from rfl), StateT.run_bind, CNorm.run_liftR,
        ← CNorm.run_callRC]
      refine WP.bind (WP.bind (WP.callRC_ok (v := b) (by rfl) ?_))
      rw [StateT.run_pure]
      refine WP.pure' ?_
      rw [hk15f, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
      refine WP.pure' ?_
      rw [hkB9, StateT.run_pure]
      refine WP.pure' ?_
      rw [C.again_rep, ite_eq_left (rfl : true = true)]
      exact ⟨⟨by omega, hc₁, by rw [C.get_set]; exact hb, hi₁⟩, .inl (by omega)⟩
  · -- a writer: the slow path
    rw [ite_eq_right hgd, StateT.run_pure]
    refine WP.pure' ?_
    rw [hkB7, StateT.run_pure]
    refine WP.pure' ?_
    rw [C.again_slow, ite_eq_right Bool.false_ne_true]
    exact ⟨hD, hc₀, .inr ⟨rfl, hi₀⟩⟩

/-- **`lockSharedUncancelable`** (`RwLockImpl.lockShared_wp`): the load, the fast loop
(`body_wp`), and the slow path under the outer mutex (`FRw.wp_addR`). The reader's heap has `R`
at the return's client parts (`FRw.Inv.rdR`). -/
theorem lockShared_wp (hW : W.Fits P UM US okM okS) (hcost : P.cost = none) (hMc : M.c = C.M.c)
    (_hLc : L.c = C.M.c) {p : Ptr} (hp : p = W.p) (t : ThreadId) (g : γ) (hg : W.Out g)
    (hokM : okM g) (_hokS : okS g) (hu : 0 < (M.part g).gh.ac.frag .unmetered)
    (hroom : ∀ G m, P.inv G m → W.ph (G t) = .out → W.nrd G m + 1 < RwState.countBound)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m)
    (_hc : m.current = t) :
    P.WP t (C.lockShared p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ (q : Frac) (H : FHeap), 0 < q.val ∧ W.R (W.xs (upd G' t g)) ⟨H, Know.none, Ghost.unit⟩ ∧
        P.inv (upd G' t (W.set (M.setPart g (rsum (M.part g) (shareRes H q))) (.rd q H))) m')
      G m d := by
  obtain ⟨hwo, hmo, hmh, hlo, hlh, hco, hso⟩ := hg
  have hmg : M.ph g ≠ .gone := by rw [hmo]; decide
  have hsc := FRw.splace_out hco hso
  obtain rfl : p = W.st.ptr := hp.trans W.ptr_st.symm
  have hret : ∀ G' m' q H, P.inv (upd G' t
      (W.set (M.setPart g (rsum (M.part g) (shareRes H q))) (.rd q H))) m' →
      W.R (W.xs (upd G' t g)) ⟨H, Know.none, Ghost.unit⟩ := fun G' m' q H h => by
    obtain ⟨rX, hI⟩ := hW.winv h
    have := hI.rdR (u := t) (by rw [upd_self, W.ph_set])
    rwa [show W.xs (upd G' t (W.set (M.setPart g (rsum (M.part g) (shareRes H q))) (.rd q H))) =
      W.xs (upd G' t g) from upd_map W.x G' t (by rw [W.x_set, W.x_part])] at this
  obtain ⟨kS, fin, hls, hslow, hkret, hfin⟩ := C.lockShared_eq
  rw [hls, lockSharedOf]
  refine wp_frame hfin ?_
  rw [StateT.run_bind]
  refine WP.bind (FRw.wp_loadW hW hmg hsc hi
    fun k₁ hk₁ G₁ m₁ b hc₁ hb hi₁ => ?_)
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (C.lsInv P t g d) (fun _ => 0) (C.lsPost P W t g d)
    (C.body_wp hW hcost t g hwo hmg hsc hu hroom d) _ G₁ m₁ k₁
    ⟨by omega, hc₁, by rw [C.get_set]; exact hb, hi₁⟩))
  rintro ⟨_, _⟩ G₂ m₂ k₂ ⟨hk₂, hc₂, ⟨rfl, q, H, hq, hi₂⟩ | ⟨rfl, hi₂⟩⟩
  · -- the fast path's return
    simp only [hkret, StateT.run_pure]
    exact WP.pure' ⟨rfl, hk₂, hc₂, q, H, hq, hret _ _ q H hi₂, hi₂⟩
  · -- the slow path: `+2^32` under the outer mutex, `away` from the semaphore's mutex from
    -- before the outer lock until after the outer unlock (`Fits.lAway`, `lUnaway`)
    simp only [hslow, slowOf, StateT.run_bind]
    refine WP.bind (WP.callMC_ptrProject (hW.projW hi₂ (by decide) (by decide)) ?_)
    refine WP.bind (WP.callC (WP.mono (fun _ G₃ m₃ k₃ h₃ => ?_)
      (C.M.lock_wp hW.m hcost (by rw [W.ptr_m, ← W.ptr_st]) hMc t (L.set g .away rnil)
        (by rw [W.pair.ph_ba, hmo]) (hW.okM_away hokM ⟨.inl hwo, hsc⟩)
        (by rw [W.pair.part_ba]; exact hu) io G₂ m₂ k₂ (hW.lAway hlo (.inl hmo) hi₂))))
    obtain ⟨hk₃, hc₃, rL, hi₃⟩ := h₃
    refine WP.bind (FRw.wp_addR hW (g := M.set (L.set g .away rnil) .holds rL)
      (by rw [(hW.ph_m _ _ _).1, W.ph_l, hwo]) (M.ph_set _ _ _)
      (by rw [hW.splace_m, hW.splace_l]; exact hsc) hroom hi₃
      fun k₄ hk₄ G₄ m₄ _ hc₄ q H hq _ hi₄ => ?_)
    rw [M.part_set, W.pair.part_ba] at hi₄
    -- `t`'s ghost value at the reader's place `y`, `away` from the semaphore's mutex
    obtain ⟨y, hyd⟩ : ∃ y, y = W.set (M.setPart g (rsum (M.part g) (shareRes H q))) (.rd q H) :=
      ⟨_, rfl⟩
    have hy : W.set (M.setPart (M.set (L.set g .away rnil) .holds rL)
        (rsum (M.part g) (shareRes H q))) (.rd q H) = M.set (L.set y .away rnil) .holds rL := by
      rw [hyd, M.setPart_set, hW.wset_m, W.pair.setPart (L.set g .away rnil), L.setPart_set,
        ← W.pair.setPart g, W.set_l]
    rw [hy] at hi₄
    have hly : L.ph y = .out := by rw [hyd, W.lph, W.pair.setPart, L.ph_setPart, hlo]
    have hlhy : L.held y = rnil := by rw [hyd, W.lheld, W.pair.setPart, L.held_setPart, hlh]
    refine WP.bind (WP.callMC_ptrProject (hW.projW hi₄ (by decide) (by decide)) ?_)
    refine WP.bind (WP.callC (WP.mono (fun _ G₅ m₅ k₅ h₅ => ?_)
      (C.M.unlock_wp hW.m hcost (by rw [W.ptr_m, ← W.ptr_st]) hMc t
        (M.set (L.set y .away rnil) .holds rL) (M.ph_set _ _ _)
        ((hW.m.ok_set _ _ _).mpr (by
          rw [hyd]
          exact hW.okM_awaySet ((hW.okM_part _ _ hsc).mpr hokM) (.inr (.inr rfl))
            (by rw [hW.splace_part]; exact hsc)))
        io G₄ m₄ k₄ hi₄ hc₄)))
    obtain ⟨hk₅, hc₅, hi₅⟩ := h₅
    rw [M.set_set] at hi₅
    replace hi₅ := hW.lBack hly hlhy (.inl rfl) hi₅
    have hmy : M.ph y = .out := by rw [hyd, hW.mph, M.ph_setPart, hmo]
    have hmhy : M.held y = rnil := by rw [hyd, hW.mheld, M.held_setPart, hmh]
    have hgo : M.set y .out rnil = y := by rw [← hmy, ← hmhy, M.set_self]
    rw [hgo, hyd] at hi₅
    simp only [StateT.run_pure]
    exact WP.pure' ⟨rfl, by omega, hc₅, q, H, hq, hret _ _ q H hi₅, hi₅⟩

/-! ## `unlockShared` -/

/-- **`unlockShared`** (`RwLockImpl.unlockShared_wp`): `-2^32` (`FRw.wp_subR`); the last reader
before a writer (`RwState.Family.last_guard`, `writing_guard`) posts the resource it carries at
the semaphore (`SemImpl.post_wp_resource`): the post makes the state `RwPosted` (`Inv.rp`: the
writer at `ww`, no other reader), the pool is the resource (`Inv.rpR`), and `US`'s stability is
the protocol's `upost`. -/
theorem unlockShared_wp (hW : W.Fits P UM US okM okS) (hcost : P.cost = none)
    (_hMc : M.c = C.M.c) (hLc : L.c = C.M.c) {p : Ptr} (hp : p = W.p) (t : ThreadId) (g : γ)
    (r₀ : Res) (q : Frac) (H : FHeap) (hrd : W.ph g = .rd q H) (hmo : M.ph g = .out)
    (hmh : M.held g = rnil) (hlo : L.ph g = .out) (hlh : L.held g = rnil) (hco : Cn.ph g = .out)
    (hso : S.ph g = .out) (hpart : M.part g = rsum r₀ (shareRes H q)) (_hokM : okM g)
    (hokS : okS g) (hu : 0 < r₀.gh.ac.frag .unmetered)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m)
    (_hc : m.current = t) :
    P.WP t (C.unlockShared p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (W.set (M.setPart g r₀) .out)) m') G m d := by
  obtain rfl : p = W.st.ptr := hp.trans W.ptr_st.symm
  obtain ⟨k1, k2, fin, hus, hk1t, hk1f, hk2, hfin⟩ := C.unlockShared_eq
  rw [hus, unlockSharedOf]
  refine wp_frame hfin ?_
  rw [StateT.run_bind]
  refine WP.bind (FRw.wp_subR hW hrd (by rw [hmo]; decide) hpart (FRw.splace_out hco hso) hi
    fun k₁ hk₁ G₁ m₁ old hc₁ hcase => ?_)
  have hlg : (old &&& (9223372032559808512 : BitVec 64) == (4294967296 : BitVec 64)) =
      (RwState.readers old == 1) := RwState.Family.last_guard (c := 31) (by decide) 1 old
  have hwg : (old &&& (1 : BitVec 64) != (0 : BitVec 64)) = RwState.writing old :=
    RwState.Family.writing_guard 31 1 old
  rw [StateT.run_bind]
  refine WP.bind ?_
  rcases hcase with ⟨hlast, hi₁⟩ | ⟨h1, hwt, r, hR, hdj, hi₁⟩
  · -- no post: other readers remain, or no writer
    split
    · rename_i hcd
      rw [hwg, hlast (by rw [hlg] at hcd; simpa using hcd), StateT.run_pure]
      refine WP.pure' ?_
      simp only [hk1f, pure_bind, hk2, StateT.run_pure]
      exact WP.pure' ⟨rfl, by omega, hc₁, hi₁⟩
    · rw [StateT.run_pure]
      refine WP.pure' ?_
      simp only [hk1f, pure_bind, hk2, StateT.run_pure]
      exact WP.pure' ⟨rfl, by omega, hc₁, hi₁⟩
  · -- the last reader before the writer: it posts the resource, `away` from the outer mutex
    -- (`Fits.mAway`, `mUnaway`)
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = W.set (M.setPart g (rsum r₀ r)) (.rp r) := ⟨_, rfl⟩
    obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = M.set g₀ .away rnil := ⟨_, rfl⟩
    obtain ⟨gy, hgy⟩ : ∃ gy, gy = W.set (M.setPart g r₀) .out := ⟨_, rfl⟩
    obtain ⟨gx, hgxd⟩ : ∃ gx, gx = M.set gy .away rnil := ⟨_, rfl⟩
    rw [← hg₀] at hi₁
    replace hi₁ := hW.mAway (by rw [hg₀, hW.mph, M.ph_setPart, hmo])
      (by rw [hg₀, W.lph, W.pair.setPart, L.ph_setPart, hlo]) hi₁
    rw [← hg₁] at hi₁
    have hcd : (old &&& (9223372032559808512 : BitVec 64) == (4294967296 : BitVec 64)) = true :=
      by rw [hlg, h1]; rfl
    rw [ite_eq_left hcd, hwg, hwt, StateT.run_pure]
    refine WP.pure' ?_
    simp only [hk1t, bind_assoc, StateT.run_bind]
    have hpgx : L.part gx = r₀ := by
      rw [hgxd, hgy, ← W.pair.part, M.part_set, hW.mpart, M.part_setPart]
    have hsplit : L.part g₁ = rsum (L.part gx) r := by
      rw [hpgx, hg₁, hg₀, ← W.pair.part, M.part_set, hW.mpart, M.part_setPart]
    have hu' : 0 < (L.part gx).gh.ac.frag .unmetered := by rw [hpgx]; exact hu
    have hgx : gx = W.set (L.setPart g₁ r₀) .out := by
      rw [hgxd, hgy, hg₁, hg₀, ← W.pair.setPart, M.setPart_set, hW.wset_m, ← hW.wset_part,
        M.setPart_setPart, W.set_set]
    have hwg₁ : W.ph g₁ = .rp r := by rw [hg₁, (hW.ph_m _ _ _).1, hg₀, W.ph_set]
    have hlg₁ : L.ph g₁ = .out := by
      rw [hg₁, W.pair.ph_ab, hg₀, W.lph, W.pair.setPart, L.ph_setPart, hlo]
    have hlgx : L.ph gx = .out := by
      rw [hgxd, W.pair.ph_ab, hgy, W.lph, W.pair.setPart, L.ph_setPart, hlo]
    have hokg₁ : okS g₁ ∧ (M.ph g₁ = .away ∨ M.ph g₁ = .holdsAway) := by
      rw [hg₁]; exact hW.okS_away (by rw [hg₀, hW.okS_set, hW.okS_part]; exact hokS)
    have hokgx : okS gx ∧ (M.ph gx = .away ∨ M.ph gx = .holdsAway) := by
      rw [hgxd]; exact hW.okS_away (by rw [hgy, hW.okS_set, hW.okS_part]; exact hokS)
    have hxs : ∀ G₂ rL, W.xs (upd G₂ t (L.set g₁ .holds rL)) = W.xs (upd G₂ t gx) :=
      fun G₂ rL => upd_map W.x G₂ t (by
        rw [hgxd, hgy, hg₁, hg₀, W.x_l, W.x_m, W.x_set, W.x_part, W.x_m, W.x_set, W.x_part])
    -- at the post the state becomes `RwPosted` and the pool the resource
    have hst : ∀ G₂ rL m₂, P.inv (upd G₂ t (L.set g₁ .holds rL)) m₂ →
        RwPosted W.ph (upd G₂ t gx) ∧ ¬ RwPosted W.ph (upd G₂ t g₁) ∧
          W.R (W.xs (upd G₂ t gx)) r := by
      intro G₂ rL m₂ h
      obtain ⟨rX, hI⟩ := hW.winv h
      have hrp : W.ph (upd G₂ t (L.set g₁ .holds rL) t) = .rp r := by
        rw [upd_self, W.ph_l, hwg₁]
      obtain ⟨h0, ⟨w, hw⟩, huq⟩ := hI.rp t (by rw [hrp]; rfl)
      have hwne : w ≠ t := by rintro rfl; rw [hrp] at hw; cases hw
      have hgo : W.ph gx = .out := by rw [hgxd, (hW.ph_m _ _ _).1, hgy, W.ph_set]
      refine ⟨⟨⟨w, by rwa [upd_ne _ _ hwne] at hw ⊢⟩, fun u => ?_, fun u => ?_⟩,
        fun ⟨_, _, h⟩ => ?_, ?_⟩
      · by_cases e : u = t
        · subst e; rw [upd_self, hgo]; rfl
        · have := FRw.noRd_of hI.ex h0 u
          rwa [upd_ne _ _ e] at this ⊢
      · by_cases e : u = t
        · subst e; rw [upd_self, hgo]; rfl
        · rw [upd_ne _ _ e]
          cases hr : (W.ph (G₂ u)).isRp
          · rfl
          · exact absurd (huq u (by rw [upd_ne _ _ e]; exact hr)) e
      · have := h t
        rw [upd_self, hwg₁] at this
        cases this
      · have := hI.rpR t r hrp
        rwa [hxs] at this
    refine WP.bind (WP.callMC_ptrProject (hW.projW hi₁ (by decide) (by decide)) ?_)
    refine WP.bind (WP.callC (WP.mono (fun _ G₂ m₂ k₂ h₂ => ?_)
      (C.S.post_wp hW.s hcost (hLc.trans C.c_eq.symm) (by rw [W.ptr_s, ← W.ptr_st])
        t g₁ gx r hlg₁
        (by rw [hg₁, (hW.ph_m _ _ _).2.1, hg₀, FRw.cph_w, (hW.ph_part _ _).2.1, hco])
        (by rw [hg₁, (hW.ph_m _ _ _).2.2, hg₀, FRw.sph_w, (hW.ph_part _ _).2.2, hso])
        hokg₁ hlgx
        (by rw [hgxd, W.pair.held_ab, hgy, W.lheld, W.pair.setPart, L.held_setPart, hlh])
        (by rw [hgxd, (hW.ph_m _ _ _).2.1, hgy, FRw.cph_w, (hW.ph_part _ _).2.1, hco])
        (by rw [hgxd, (hW.ph_m _ _ _).2.2, hgy, FRw.sph_w, (hW.ph_part _ _).2.2, hso])
        hokgx hsplit (by rw [hpgx]; exact hdj)
        (fun G₂ rL m₂ h₂ => by
          obtain ⟨hp, hnp, -⟩ := hst G₂ rL m₂ h₂
          rw [W.cnt_posted _ hp, W.cnt_idle _ hnp]
          decide)
        (fun G₂ rL m₂ h₂ x hx => by
          obtain ⟨hp, hnp, hR'⟩ := hst G₂ rL m₂ h₂
          rw [W.pool_idle _ hnp] at hx
          have hxr : x = r := (sep_emp.mp hx :)
          subst hxr
          rw [W.pool_posted _ hp]
          exact hR')
        (fun G₂ rX m₂ h₁ h₂ sh sc hUS hL hS hC => by
          rw [hgx] at hL hS hC ⊢
          exact hW.upost G₂ rX m₂ t g₁ r₀ r h₁ h₂ sh sc hwg₁ hUS hL hS hC)
        io G₁ m₁ k₁ hu' hi₁ hc₁)))
    obtain ⟨hk₂, hc₂, hi₂⟩ := h₂
    -- back at the outer mutex's `out`
    replace hi₂ := hW.mUnaway (by rw [hgxd, M.ph_set]) hlgx hi₂
    have hmy : M.ph gy = .out := by rw [hgy, hW.mph, M.ph_setPart, hmo]
    have hmhy : M.held gy = rnil := by rw [hgy, hW.mheld, M.held_setPart, hmh]
    have hgo : M.set gx .out rnil = gy := by rw [hgxd, M.set_set, ← hmy, ← hmhy, M.set_self]
    rw [hgo, hgy] at hi₂
    simp only [StateT.run_pure, pure_bind, hk2]
    exact WP.pure' ⟨rfl, by omega, hc₂, hi₂⟩

/-- **`Io.RwLock` is a reader/writer lock** (`RwLockImpl`), in every program whose code it is. -/
def impl : RwLockImpl Tgt where
  lock := C.lock
  unlock := C.unlock
  lockShared := C.lockShared
  unlockShared := C.unlockShared
  c := C.M.c
  lockShared_wp := C.lockShared_wp
  unlockShared_wp := C.unlockShared_wp
  lock_wp := C.lock_wp
  unlock_wp := C.unlock_wp

end IoRwLockCode

end Full
end Zig
