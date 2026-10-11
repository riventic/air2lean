import ZigLean.Conc.Unroll
import Proofs.Sync.RwLockContract

/-!
# Snapshot-pair generated-client proofs

This file uses ROOT's actual exported `rwLockSnapshotPair` definition, preserving its full
profile header. The proofs establish same-hold reads, release, writer join and stack
reclamation using the existing restricted protocol. The all-fuel/all-oracle result and
strict safety theorems are kernel-checked for the 0.16.0 Linux translation
(`docs/theorem-inventory.md`).
-/

open Zig Zig.Conc Zig.Conc.Proto Sync Assn
open Sync.RwLockRead

namespace Sync.RwLockSnapshotPair

-- As in `Proofs/Sync/RwLock.lean`: unification must not unfold `WP` into the program.
attribute [local irreducible] Proto.WP

/-- Instantiation of the reusable same-hold contract for the second client's snapshot
fragment. This is a real ownership/WP contract, not by itself a theorem of the new
exported `rwLockSnapshotPair`: the program proof below additionally composes its
acquire/release, initialization, join and reclamation boundaries. -/
abbrev snapshot_fragment_wp := @RwLockContract.held_pair_wp

/-- Two observations of the same protected count produce precisely the expected result set.
Equality of the observations is a premise, not an assumption inferred from two lock calls. -/
theorem result_of_same_snapshot {first second : Nat}
    (hfirst : first ≤ 2) (hsame : second = first) :
    BitVec.ofNat 32 (10 * first + second) = 0 ∨
    BitVec.ofNat 32 (10 * first + second) = 11 ∨
    BitVec.ofNat 32 (10 * first + second) = 22 := by
  subst second
  have h : first = 0 ∨ first = 1 ∨ first = 2 := by omega
  rcases h with rfl | rfl | rfl <;> simp

/-- Literal negative oracle for the planned split-acquisition interleaving: first 0,
second 1 yields 1, outside the same-hold result set. This is not a scheduler witness. -/
theorem split_snapshot_result_rejected :
    ¬ ((BitVec.ofNat 32 (10 * 0 + 1) = 0) ∨
       (BitVec.ofNat 32 (10 * 0 + 1) = 11) ∨
       (BitVec.ofNat 32 (10 * 0 + 1) = 22)) := by decide

/-- New client result predicate includes the task-lifetime obligation. -/
def QPair : Except ErrName (BitVec 32) → (ThreadId → Gh SPh) → Mem → Nat → Prop :=
  fun v _ m _ => (v = .ok 0 ∨ v = .ok 11 ∨ v = .ok 22) ∧ joinedAll 0 m

/-- WP of ROOT's actual exported client, using the existing initialization and
primitive contracts. -/
theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    (proto E₀).WP 0 (rwLockSnapshotPair io) QPair G0 { mem0 σ with current := 0 } d := by
  unfold rwLockSnapshotPair
  -- the `Shared`: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 64 8 (by decide))
    (Owned.start rfl rfl) rfl (by simp [mem0, Mem.ofGlobals]) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = bPtr from rfl] at hb₁ ⊢
  -- its four parts
  obtain ⟨hI, hR₁, dI, rfl, hI₁, hR₁'⟩ := bytesAt_split hb₁ (k := 16) (by simp)
  obtain ⟨hS, hR₂, dS, rfl, hS₁, hR₂'⟩ := bytesAt_split hR₁' (k := 40) (by simp)
  obtain ⟨hN, hP, dN, rfl, hN₁, hP₁⟩ := bytesAt_split hR₂' (k := 4) (by simp)
  have hsI : ((Array.replicate 64 Byte.undef).extract 0 16).size = 16 := by simp
  have hsS : (((Array.replicate 64 Byte.undef).extract 16).extract 0 40).size = 40 := by simp
  have hsN : ((((Array.replicate 64 Byte.undef).extract 16).extract 40).extract 0 4).size = 4 := by
    simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- the stores: `io`, the `RwLock`, `n`
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 (hI ∪ (hS ∪ (hN ∪ hP)))) m₁ := ho₁
  have F₁ : (bytesAt bPtr A 64 .stack ((Array.replicate 64 Byte.undef).extract 0 16) ∗
      (bytesAt (bPtr.add 16) A 64 .stack (((Array.replicate 64 Byte.undef).extract 16).extract 0 40) ∗
        (bytesAt ((bPtr.add 16).add 40) A 64 .stack
          ((((Array.replicate 64 Byte.undef).extract 16).extract 40).extract 0 4) ∗
         bytesAt (((bPtr.add 16).add 40).add 4) A 64 .stack
          ((((Array.replicate 64 Byte.undef).extract 16).extract 40).extract 4))))
      (hI ∪ (hS ∪ (hN ∪ hP))) := ⟨hI, _, dI, rfl, hI₁, hS, _, dS, rfl, hS₁, hN, hP, dN, rfl, hN₁, hP₁⟩
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := bPtr) (A := A) (S := 64) (K := .stack) (k := 0)
    (a := 8) io rfl (by decide) (by rw [hsI]; decide) (by simp [bPtr]; omega) (by decide)).frame)
    ho₁' hc₁ (by rw [hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₁)
    fun _ m₂ h₂ _ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  -- `&shared.rw`, formed in bounds of `io`'s bytes (`ptrProject`, MM-3)
  have hs₂' : h₂.Sub m₂.heap := by simpa [upd_self] using ho₂.sub 0
  have hwI : (writeBytes ((Array.replicate 64 Byte.undef).extract 0 16) 0 (Enc.encode io)).size = 16 := by
    rw [writeBytes_size _ _ _ (by simp [enc_io])]; exact hsI
  have pr₂ : (ptrProject bPtr (·.add 16)).run m₂ = pure (bPtr.add 16, m₂) := by
    obtain ⟨hx, hy, dxy, hxy, hbx, -⟩ := F₂
    rw [hxy] at hs₂'
    exact bytesAt_ptrProject_sub hbx (Heap.sub_union_left.trans hs₂') (k := 16) (by rw [hwI]; exact Nat.le_refl _) (by rw [hwI]; decide)
  refine WP.bind (WP.callMC_ptrProject pr₂ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := bPtr.add 16) (A := A) (S := 64) (K := .stack)
    (k := 0) (a := 8) rw0 (by rw [rw_size]; rfl) rfl (by decide)
    (by rw [hsS]; decide) (by simp [bPtr, Ptr.add]; omega) (by decide)).frame.frameL) ho₂
    (hs₂.current.trans hc₁) (by rw [hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₂)
    fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  -- `&shared.n`, formed in bounds (`ptrProject`, MM-3)
  have hs₃' : h₃.Sub m₃.heap := by simpa [upd_self] using ho₃.sub 0
  have pr₃ : (ptrProject bPtr (·.add 56)).run m₃ = pure ((bPtr.add 16).add 40, m₃) := by
    obtain ⟨hx, hy, dxy, hxy, hbx, hyy⟩ := F₃
    obtain ⟨hz, hw, dzw, hzw, -, hww⟩ := hyy
    obtain ⟨hn, hp', dnp, hnw, hbn, -⟩ := hww
    rw [hxy] at hs₃'
    have hsy : hy.Sub m₃.heap := (Heap.sub_union_right dxy).trans hs₃'
    rw [hzw] at hsy
    have hsw : hw.Sub m₃.heap := (Heap.sub_union_right dzw).trans hsy
    rw [hnw] at hsw
    have i0 : m₃.inBounds bPtr = true := by
      simpa using bytesAt_inBounds_sub hbx (Heap.sub_union_left.trans hs₃') (k := 0) (by simp)
        (by rw [hwI]; decide)
    have i56 : m₃.inBounds ((bPtr.add 16).add 40) = true := by
      simpa using bytesAt_inBounds_sub hbn (Heap.sub_union_left.trans hsw) (k := 0) (by simp)
        (by simp)
    exact ptrProject_add_run i0 i56
  refine WP.bind (WP.callMC_ptrProject pr₃ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := (bPtr.add 16).add 40) (A := A) (S := 64)
    (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsN]; decide)
    (by simp [bPtr, Ptr.add]; omega) (by decide)).frame.frameL.frameL) ho₃
    (hs₃.current.trans (hs₂.current.trans hc₁))
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₃)
    fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  have hth₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₄ : m₄.atomics = #[] := by rw [hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₄ : m₄.waiters = #[] := by rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hPa : Parts io A ((((Array.replicate 64 Byte.undef).extract 16).extract 40).extract 4) h₄ := by
    rw [writeBytes_all (by rw [hsI, enc_io]), writeBytes_all (by rw [hsS, rw_size]),
      writeBytes_all (by rw [hsN, enc_u32])] at F₄
    exact F₄
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, inv_pre ho₄ hPa hA8 hth₄ hat₄ hq₄, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gA (.wo 0) Heap.empty default, ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₆, hi₆⟩ := inv_spawn hi₅ hg₁ hf
  -- One acquire, both actual generated plain loads, then release.
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (projB hi₆ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (lockS_spec spec₀ hi₆)))
  rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, h, hi₂⟩
  refine WP.bind (WP.callMC_ptrProject (projB hi₂ (k := 56) (by decide)) ?_)
  dsimp only
  rw [show bPtr.add 56 = nPtr from rfl]
  have hW := w_isW hi₂.2.1 (by rw [upd_self]; simp [gA])
  rw [upd0_1] at hW
  have hk : (G₂ 1).2.2.cnt ≤ 2 := cnt_le hW
  refine WP.bind (wp_n spec₀ (y := .sh false) hi₂ hc₂ rfl (.inl rfl)
    (TTriple.load (by decide)) fun m₃ h₃ hc₃ ht₃ hi₃ => ?_)
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (projB hi₃ (k := 56) (by decide)) ?_)
  dsimp only
  rw [show bPtr.add 56 = nPtr from rfl]
  refine WP.bind (wp_n spec₀ (y := .sh false) hi₃ hc₃ rfl (.inl rfl)
    (TTriple.load (by decide)) fun m₄ h₄ hc₄ ht₄ hi₄ => ?_)
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (projB hi₄ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (unlockS_spec spec₀ hi₄)))
  rintro _ G₅ m₅ d₅ ⟨hd₅, hc₅, hi₅⟩
  -- the join
  have hiJ := inv_g0 spec₀.frame (y := .joins) hi₅ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨fun _ _ => .inr rfl, (fun h => by cases h), (fun h => by cases h.1), (fun _ _ h => by cases h),
      (fun h => by cases h)⟩
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨gA .joins Heap.empty default, hiJ, fun G₃ m₈ hg₃ hi₈ => ?_⟩)
  obtain ⟨-, ⟨-, h0, -⟩ | ⟨hs2, hr1, -, -, -⟩⟩ := hi₈.2.1.shape
  · exfalso; change (G₃ 0).2.2 = _ at h0; rw [hg₃] at h0; cases h0
  have hr1' : m₈.threads[1]? = some { spawner := 0, joined := false } := by
    rcases hr1 with ⟨h, -⟩ | ⟨-, -, hj⟩
    · exact h
    · change (G₃ 0).2.2.jd = true at hj; rw [hg₃] at hj; cases hj
  refine ⟨fun _ => ⟨by decide, by rw [hs2]; decide, ⟨rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr1']⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₈ with current := 0 }) hr1' rfl rfl, fun m₉ hj => ?_⟩⟩
  have hi₉ := inv_join hi₈ hg₃ hfin hj
  have hc₉ : m₉.current = 0 := by obtain ⟨_, _, _, rfl⟩ := Proto.join_eq hj; rfl
  -- Both saved values are the same count from the held phase, even if the
  -- writer increments again after unlock and before its join.
  have h3 : (G₂ 1).2.2.cnt = 0 ∨ (G₂ 1).2.2.cnt = 1 ∨
      (G₂ 1).2.2.cnt = 2 := by omega
  refine WP.bind (WP.callRC_ok (v := BitVec.ofNat 32 (10 * (G₂ 1).2.2.cnt))
    (by rcases h3 with hk | hk | hk <;> simp only [upd0_1, hk] <;> rfl) ?_)
  refine WP.bind (WP.callRC_ok
    (v := BitVec.ofNat 32 (10 * (G₂ 1).2.2.cnt + (G₂ 1).2.2.cnt))
    (by rcases h3 with hk | hk | hk <;> simp only [upd0_1, hk] <;> rfl) ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  refine WP.bind (WP.mono ?_ (RwLockContract.reclaim_joined_wp hi₉ rfl hc₉))
  rintro _ G₄ m₁₀ d₄ ⟨_, hj⟩
  refine WP.pure' ⟨?_, hj⟩
  rcases h3 with h0 | h1 | h2 <;> simp_all [QPair]

/-- Successful results of the actual exported second client, for every fuel/oracle. -/
theorem snapshotPair_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 0 ∨ v = .ok 11 ∨ v = .ok 22 := by
  obtain ⟨_, _, hv, _⟩ := (proto E₀).run_sound env (Proto.of_available henv) dispatch G0 (dispatch_spec spec₀)
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- Strict scheduler safety of the actual exported second client, for every fuel/oracle.
No fairness or termination is asserted. -/
theorem snapshotPair_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run ≠ some (.error e) :=
  (proto E₀).run_safe env (Proto.of_available henv) dispatch G0 rfl (dispatch_spec spec₀)
    (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the snapshot-pair reader returns 0 (both reads before the writer) within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem snapshotPair_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (rwLockSnapshotPair ⟨⟩) (mem0 σ)) = some 0 :=
  ⟨.fresh, by unroll_sched 10⟩

end Sync.RwLockSnapshotPair
