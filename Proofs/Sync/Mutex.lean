import Proofs.MutexCounter.Protocol
import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.AutoWP
import ZigLean.Conc.Unroll

/-!
# `mutexCounter` over all schedules

`mutexCounter` spawns one thread; each of the two threads adds 1 two times to a counter, under
an `Io.Mutex` (translated from Zig 0.16.0's std code; the 0.17.0 translation of this program is
the same code; the futex under it is the model). The result is 4 under every schedule
(`mutexCounter_spec`), and no schedule gives an error (`mutexCounter_safe`): no data race on the
counter, and no deadlock at the futex.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`) and uses only
the mutex contract (`MutexImpl`): this program's `Io.Mutex` is `Sync.ioMutex`. The protocol and
its steps are once for every version (`Proofs/MutexCounter/Protocol.lean`); this file gives the
`Counter`'s layout (`lo`: `io` at 0, the mutex at 16, the counter at 20) and walks `work` (by
`fsym`, with the protocol's steps and the mutex contract as rules) and `main`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.MutexCounter Sync

namespace Sync.MutexCounter

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- The `Counter`'s layout (module doc). -/
def lo : Layout where
  size := 24
  align := 8
  io := 16
  mo := 16
  c := 2
  c_ok := by decide
  ok := by decide

/-- The kid's argument. -/
def workOf : Tgt → Option Ptr
  | .work p => some p
  | _ => none

/-- This program's protocol. -/
abbrev P : Proto Tgt Gh := proto lo workOf

/-! ## `work` -/

/-- `work`'s loop invariant: thread `t` did `local1` increments and is out of the lock's code. -/
def workInv (t : ThreadId) (s : workLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = t ∧ ∃ k, P.inv (upd G t (gOut k)) m ∧ s.local1.toNat = k ∧ k ≤ 2

/-- `work`'s loop ends after 2 increments. -/
def workPost (t : ThreadId) (r : workExit × workLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  r.1 = .br3 ∧ m.current = t ∧ ∃ k, P.inv (upd G t (gOut k)) m ∧ k = 2

/-- One run of `work`'s loop: `io`, `lock`, the increment of the counter, `io`, `unlock`. Walked
by `fsym` in its `WP` mode, with the protocol's steps and the mutex contract as rules. -/
theorem loop4_body (t : ThreadId) (s : workLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : workInv t s G m d) :
    P.WP t ((work.loop4 cPtr).run s) (fun r G' m' d' =>
      if work.again4 r.1 then workInv t r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : workLocals) => 0) s)
      else workPost t r G' m' d') G m d := by
  obtain ⟨hc, k, hi, hk, hle⟩ := h
  unfold work.loop4
  fsym [WP.liftMem_pure (projI (Lo := lo) (workOf := workOf) _ _) rfl,
    (fits (Lo := lo) (workOf := workOf)).wp_readRest rfl (by decide)
      (io_rest (a := 8) rfl (by decide)) (fun _ _ _ hu => hu.io) (io_cov rfl)
      (fun _ _ _ hu => U_rec _ hu),
    ioMutex.lock_wp (fits (Lo := lo) (workOf := workOf)) rfl rfl rfl,
    ioMutex.unlock_wp (fits (Lo := lo) (workOf := workOf)) rfl rfl rfl,
    wp_load (Lo := lo) (workOf := workOf), wp_store (Lo := lo) (workOf := workOf),
    set_out, set_hold, ph_out, ph_hold, work.again4]

/-- `work`: two runs of its loop. -/
theorem work_spec (t : ThreadId) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (gOut 0)) m) (hc : m.current = t) :
    P.WP t (work cPtr) (fun _ G' m' _ => m'.current = t ∧ P.inv (upd G' t (gOut 2)) m') G m d := by
  unfold work
  fsym [WP.loop _ _ (workInv t) (fun _ => 0) (workPost t) (loop4_body t)]

/-- The kid: `work` on the `Counter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : P.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : P.inv G m) :
    P.WP u (dispatch tgt) (P.QKid u) G { m with current := u } d := by
  cases tgt with
  | work p =>
    obtain ⟨hp, rfl⟩ := hg
    obtain rfl : p = cPtr := Option.some.inj hp
    have hu1 : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      have := (shape_work hU.shape (t := u) (k := 0) (by show (G u).2 = _; rw [hgu])).1
      unfold ThreadId at *; omega
    subst hu1
    show P.WP 1 ((fun _ => ()) <$> work cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (work_spec 1 G _ d
      (by rw [show gOut 0 = G 1 from hgu.symm, upd_same]
          exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact qkid hi'
  | producer p => exact absurd hg.1 (by simp [workOf])
  | writer p => exact absurd hg.1 (by simp [workOf])
  | semWork p => exact absurd hg.1 (by simp [workOf])

/-! ## `main` -/

/-- The initial mutex. -/
def mutex0 : Io_Mutex := { state := { raw := Io_Mutex_State.unlocked } }

theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    P.WP 0 (mutexCounter io) QM G0 { mem0 σ with current := 0 } d := by
  cases io
  unfold mutexCounter
  have ht0 : ({ mem0 σ with current := 0 } : Mem).threads = #[{ spawner := 0, joined := true }] :=
    rfl
  -- the `Counter`: block 0, a stack block; `main` gives up the plain mode
  refine WP.bind (WP.liftMem_fownedS (by fsym [FTriple.allocStackDrop] : FTTriple plain _ _)
    (FOwned.start0_plain σ) rfl (by rw [ht0]; decide) (by rw [plainOwn_zero]; exact plain_intro)
    fun s1 m₁ r₁ _ hr₁ ho₁ hq₁ hs₁ => ?_)
  simp only [plainOwn, upd_upd] at ho₁
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, b, hq₁⟩ := hq₁
  obtain ⟨⟨hpb, -, hA8⟩, F₁⟩ := Full.sep_lift.mp hq₁
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl]
    at F₁ ⊢
  have hc₁ : m₁.current = 0 := hs₁.current
  have ht₁ : m₁.threads = #[{ spawner := 0, joined := true }] := hs₁.threads.trans ht0
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `io`
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := cPtr) (A := A) (S := 24)
    (K := .stack) (k := 0) (a := 8) (⟨⟩ : Io) rfl rfl (by decide) (by decide)
    (by simp [cPtr]; omega) (by decide)) ho₁ hc₁ (by rw [ht₁]; decide)
    F₁ fun _ m₂ r₂ _ hr₂ ho₂ F₂ hs₂ => ?_)
  rw [upd_upd] at ho₂
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  have ht₂ : m₂.threads = #[{ spawner := 0, joined := true }] := hs₂.threads.trans ht₁
  -- the mutex
  refine WP.bind (WP.callMC_ptrProject (projO ho₂ (by rw [ht₂]; decide)
    F₂ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt' (p := cPtr) (A := A) (S := 24)
    (K := .stack) (k := 16) (a := 4) mutex0 (by decide +kernel) rfl rfl (by decide)
    (by decide +kernel) (by simp [cPtr]; omega) (by decide)) ho₂ hc₂ (by rw [ht₂]; decide)
    F₂ fun _ m₃ r₃ _ hr₃ ho₃ F₃ hs₃ => ?_)
  rw [upd_upd] at ho₃
  have hc₃ : m₃.current = 0 := hs₃.current.trans hc₂
  have ht₃ : m₃.threads = #[{ spawner := 0, joined := true }] := hs₃.threads.trans ht₂
  -- the counter
  refine WP.bind (WP.callMC_ptrProject (projO ho₃ (by rw [ht₃]; decide)
    F₃ (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := cPtr) (A := A) (S := 24)
    (K := .stack) (k := 20) (a := 4) (0 : BitVec 32) rfl rfl (by decide) (by decide +kernel)
    (by simp [cPtr]; omega) (by decide)) ho₃ hc₃ (by rw [ht₃]; decide)
    F₃ fun _ m₄ r₄ _ hr₄ ho₄ F₄ hs₄ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans hc₃
  have ht₄ : m₄.threads = #[{ spawner := 0, joined := true }] := hs₄.threads.trans ht₃
  have hat₄ : m₄.atomics = #[] := by
    rw [store_atomics hr₄, store_atomics hr₃, store_atomics hr₂, hm₁e]; rfl
  have hq₄ : m₄.waiters = #[] := by
    rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hi₀ := inv_start (Lo := lo) (workOf := workOf) ho₄ F₄ (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (fun _ => by decide +kernel) hA8 ht₄ hat₄ hq₄
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, hi₀, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gOut 0, ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₆, hi₆⟩ := inv_spawn hi₅ hg₁ hf
  dsimp only
  simp only [StateT.run_bind]
  -- `work`
  refine WP.bind (WP.callC (WP.mono ?_ (work_spec 0 _ _ k hi₆ hc₆)))
  rintro _ G₂ m₇ d₂ ⟨hc₇, hi₇⟩
  -- the join of the kid; `main` takes the counter back
  refine WP.bind (wp_join (inv_end hi₇ (.inl ⟨rfl, rfl⟩))
    fun k₂ G₃ m₈ own rX r hk₂ hc₈ ho hp hb₈ hcl₈ hja hs₈ _ => ?_)
  -- the counter holds 4
  refine WP.bind (WP.callMC_ptrProject (proj hb₈ (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_fowned
    (by fsym : FTTriple (up (pts (cPtr.add 20) 4 (BitVec.ofNat 32 4))) _ _).frame.frameL ho hc₈
    (by rw [hs₈]; decide)
    (by rw [upd_self]; exact hp) fun a m₉ r' hr ho' hq _ _ => ?_)
  obtain ⟨-, -, -, -, -, ⟨r₃, -, -, -, hq₃, -⟩⟩ := hq
  obtain ⟨rfl, -⟩ := Full.sep_lift.mp hq₃
  obtain ⟨b, blk, o, -, -, -, hm₉⟩ := load_ok hr
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the free of the `Counter`
  have hb₉ : BlkOk lo m₉ := by
    obtain ⟨blk₀, h1, h2, h3, h4⟩ := hb₈; exact ⟨blk₀, by rw [hm₉, Mem.readAt_blocks]; exact h1, h2, h3, h4⟩
  refine WP.bind (wp_free hb₉ (by rw [hm₉]; exact hcl₈.readAt _ _ _ _ _) fun m₁₀ hth => ?_)
  have hth₉ : m₉.threads = m₈.threads := by rw [hm₉, Mem.readAt_threads]
  exact WP.pure' ⟨rfl, fun r hr hsp => hja r (by rw [← hth₉, ← hth]; exact hr) hsp⟩

/-! ## The results -/

/-- **`mutexCounter` gives 4 under every schedule** (every oracle `o`, every `fuel`). -/
theorem mutexCounter_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env dispatch fuel o (mutexCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 4 := by
  obtain ⟨_, _, hv, -⟩ := P.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- **No run of `mutexCounter` gives an error**: no data race on the counter, no deadlock at the
futex, no panic, under every schedule. -/
theorem mutexCounter_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (mutexCounter io) (mem0 σ)).run ≠ some (.error e) :=
  P.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the mutex counter returns 4 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem mutexCounter_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (mutexCounter ⟨⟩) (mem0 σ)) = some 4 :=
  ⟨.fresh, by unroll_sched 10⟩

end Sync.MutexCounter
