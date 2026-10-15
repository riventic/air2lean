import Proofs.Handoff.Ops
import Proofs.Threadsync.Cond
import Proofs.Threadsync.Event
import ZigLean.Conc.Unroll
import ZigLean.Sep.Full.Auto

/-!
# `threadsync.handoff` over all schedules

`handoff` spawns a producer. The producer sets `v = 7` and `ready = true` under a `Thread.Mutex`,
signals a `Thread.Condition` and sets a `Thread.ResetEvent`. `main` waits on the condition until
`ready`, reads `v`, waits on the event and joins the producer. All three sync objects are translated
from Zig 0.15.2's std code (Linux, macOS, aarch64-linux); the futex under them is the model. The
result is 7 under every schedule (`handoff_spec`), and no schedule gives an error (`handoff_safe`):
no data race, no deadlock at a futex, no `unreachable`.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`) and uses only
the contracts of the sync objects (`MutexImpl`, `CondImpl`, `EventImpl`): this program's
`Thread.Mutex`, `Thread.Condition` and `Thread.ResetEvent` are `Threadsync.threadMutex`,
`Threadsync.threadCond` and `Threadsync.resetEvent`. The protocol and its steps are once for every
version (`Proofs/Handoff/`, the same as `Proofs/Sync/Handoff.lean`'s); this file gives the `Box`'s
layout (`lo`: no `io`, the mutex at 0, the condition's state and epoch at 4 and 8, the event at
12, `v` at 16, `ready` at 20) and walks `main` and the producer of the generated code.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Handoff Threadsync

namespace Threadsync.HO

-- `main`'s condition and event waits reach the translated `std.time.Timer` (OSK-01): the results
-- hold for every OS environment.
variable [Zig.Os.HasEnv]

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- The `Box`'s layout (module doc); the mutex's contended value is the OS's (`mutexC`). -/
def lo : Layout where
  size := 24
  align := 4
  io := 0
  mo := 0
  so := 4
  vo := 12
  xo := 16
  ro := 20
  c := mutexC
  c_ok := by decide
  ok := by decide

/-- The producer's argument. -/
def prodOf : Tgt → Option Ptr
  | .producer p => some p
  | _ => none

/-! ## The producer -/

theorem producer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : (proto lo prodOf).inv (upd G 1 (gO rnil { ph := .lk })) m) (_hc : m.current = 1) :
    (proto lo prodOf).WP 1 (producer bPtr) (fun _ G' m' _ => m'.current = 1 ∧
      (proto lo prodOf).inv (upd G' 1 (⟨.gone, rnil, rnil⟩, { ph := .fin })) m') G m d := by
  unfold producer
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (wp_lockP threadMutex rfl rfl ⟨⟩ hi)))
  rintro _ G₂ m₂ d₂ ⟨-, hc₂, rL, hi₂⟩
  -- `v = 7`, `ready = true`
  refine WP.bind (WP.callMC_ptrProject (projI hi₂ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_storeV hi₂ hc₂ fun m₃ rL₃ hc₃ hi₃ => ?_)
  refine WP.bind (WP.callMC_ptrProject (projI hi₃ (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_storeR hi₃ hc₃ fun m₄ rL₄ hc₄ hi₄ => ?_)
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (wp_unlockP threadMutex rfl rfl ⟨⟩ hi₄ hc₄)))
  rintro _ G₃ m₆ d₃ ⟨-, hc₆, hi₆⟩
  -- `signal`
  refine WP.bind (WP.callMC_ptrProject (projI hi₆ (k := 4) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (wp_signal threadCond rfl ⟨⟩ hi₆)))
  rintro _ G₄ m₈ d₄ ⟨-, hc₈, hi₈⟩
  -- `set`
  refine WP.bind (WP.callMC_ptrProject (projI hi₈ (k := 12) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (wp_set resetEvent rfl ⟨⟩ hi₈)))
  rintro _ G₅ m₁₀ d₅ ⟨-, hc₁₀, hi₁₀⟩
  repeat (first
    | exact ⟨hc₁₀, hi₁₀⟩
    | refine WP.pure' ?_
    | simp only [StateT.run_pure])
  done

omit [Zig.Os.HasEnv] in
theorem discard_eq (x : ConcM Tgt Unit) : discard x = (fun _ => ()) <$> x := rfl

omit [Zig.Os.HasEnv] in
theorem dispatch_producer (p : Ptr) : dispatch (Tgt.producer p) = (fun _ => ()) <$> producer p := by
  rw [show dispatch (Tgt.producer p) = discard (producer p) from rfl]; exact discard_eq _

/-- The producer: its code, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto lo prodOf).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (proto lo prodOf).inv G m) :
    (proto lo prodOf).WP u (dispatch tgt) ((proto lo prodOf).QKid u) G { m with current := u } d := by
  cases tgt with
  | producer p =>
    obtain ⟨hp, rfl⟩ := hg
    obtain rfl : p = bPtr := Option.some.inj hp
    have hu1 : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      exact hU.shape.one (u := u) (by show (G u).2.ph.isProd = true; rw [hgu]; rfl)
    subst hu1
    rw [dispatch_producer]
    refine WP.map (WP.mono ?_ (producer_spec G _ d
      (by rw [show gO rnil { ph := .lk } = G 1 from hgu.symm, upd_same]
          exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact qkid hi'
  | work p => exact absurd hg.1 (by simp [prodOf])
  | task p => exact absurd hg.1 (by simp [prodOf])

/-! ## `main` -/

/-- The `ready` loop's invariant: `main` holds the mutex at `run`. -/
def inv12 (rM : Res) (_ : handoffLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = 0 ∧ ∃ rL, (proto lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m

/-- The `ready` loop ends: `main` read `ready = true`. -/
def post12 (rM : Res) (r : handoffExit × handoffLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  r.1 = .br11 ∧ m.current = 0 ∧ ∃ rL, (proto lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m ∧
    (G 1).2.ph.hasR = true

theorem loop12_body (rM : Res) (hpl : rM.Plain) (s : handoffLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv12 rM s G m d) :
    (proto lo prodOf).WP 0 ((handoff.loop12 bPtr).run s) (fun r G' m' d' =>
      if handoff.again12 r.1 then inv12 rM r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : handoffLocals) => 0) s)
      else post12 rM r G' m' d') G m d := by
  obtain ⟨hc, rL, hi⟩ := h
  unfold handoff.loop12
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  refine WP.bind (WP.bind (WP.callMC_ptrProject (projI hi (k := 20) (by decide)) ?_))
  dsimp only
  refine WP.bind (wp_loadR hi hc fun m' rQ hc' hi' => ?_)
  cases hr : (G 1).2.ph.hasR
  · -- `ready = false`: the condition wait
    simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_pure]
    refine WP.bind (WP.callMC_ptrProject (projI hi' (k := 4) (by decide)) ?_)
    dsimp only
    refine WP.bind (WP.callC (WP.mono ?_ (wp_cwait threadCond rfl rfl rfl ⟨⟩ hpl hi' hc' hr)))
    rintro _ G₁ m₁ d₁ ⟨hd₁, hc₁, rL₁, hi₁⟩
    repeat (first
      | exact ⟨⟨hc₁, rL₁, hi₁⟩, .inl hd₁⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, handoff.again12, ↓reduceIte])
    done
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    repeat (first
      | exact ⟨rfl, hc', rQ, hi', hr⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, handoff.again12, Bool.false_eq_true, ↓reduceIte])
    done

/-- The `Box` that `main` stores. -/
def box0 : Box :=
  { m := mutexOf 0,
    c := { impl := { state := { raw := 0 }, epoch := { raw := 0 } } }, ready := false,
    done := { impl := { state := { raw := 0 } } }, v := 0 }

theorem main_spec (σ : Placement) (d : Nat) :
    (proto lo prodOf).WP 0 handoff QM G0 { mem0 σ with current := 0 } d := by
  unfold handoff
  have ht0 : ({ mem0 σ with current := 0 } : Mem).threads = #[{ spawner := 0, joined := true }] :=
    rfl
  -- the `Box`: block 0, a stack block in the plain mode, which `main` keeps
  refine WP.bind (WP.liftMem_fownedS (by fsym : FTTriple plain _ _)
    (FOwned.start0_plain σ) rfl (by rw [ht0]; decide) (by rw [plainOwn_zero]; exact plain_intro)
    fun s0 m₁ r₁ _ hr₁ ho₁ hq₁ hs₁ => ?_)
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, b, hq₁⟩ := hq₁
  obtain ⟨⟨hpb, -, hA4⟩, F₁⟩ := Full.sep_lift.mp hq₁
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = bPtr from rfl]
    at F₁ ⊢
  have hc₁ : m₁.current = 0 := hs₁.current
  have ht₁ : m₁.threads = #[{ spawner := 0, joined := true }] := hs₁.threads.trans ht0
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- the `Box`'s store
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt' (p := bPtr) (A := A) (S := 24)
    (K := .stack) (k := 0) (a := 4) box0 (by decide +kernel) rfl rfl (by decide)
    (by decide +kernel) (by simp [bPtr]; omega) (by decide)).frame ho₁ hc₁ (by rw [ht₁]; decide)
    F₁ fun _ m₂ r₂ _ hr₂ ho₂ F₂ hs₂ => ?_)
  simp only [plainOwn, upd_upd] at ho₂
  have ht₂ : m₂.threads = #[{ spawner := 0, joined := true }] := hs₂.threads.trans ht₁
  have hat₂ : m₂.atomics = #[] := by rw [store_atomics hr₂, hm₁e]; rfl
  have hq₂ : m₂.waiters = #[] := by rw [hs₂.waiters, hs₁.waiters]; rfl
  obtain ⟨rM, hplM, hi₀⟩ := inv_of_box (Lo := lo) (prodOf := prodOf) ho₂ F₂ (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun h => absurd h (by decide)) hA4 ht₂ hat₂ hq₂
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gO rM { ph := .pre }, hi₀, fun G₁ m₈ hg₁ hi₈ =>
    ⟨gO rnil { ph := .lk }, ⟨rfl, rfl⟩, fun child m₉ hf => ?_⟩⟩)
  obtain ⟨rfl, hi₉⟩ := inv_spawn hi₈ hg₁ hf
  dsimp only
  simp only [StateT.run_bind]
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (wp_lockM threadMutex rfl rfl ⟨⟩ hi₉)))
  rintro _ G₂ m₁₀ d₂ ⟨-, hc₁₀, rL, hi₁₀⟩
  -- the `ready` loop
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv12 rM) (fun _ => 0) (post12 rM) (loop12_body rM hplM) _
    G₂ m₁₀ d₂ ⟨hc₁₀, rL, hi₁₀⟩))
  rintro ⟨e, s'⟩ G₃ m₁₁ d₃ ⟨rfl, hc₁₁, rL₁, hi₁₁, hr⟩
  dsimp only
  simp only [StateT.run_bind]
  -- `v`: the producer stored 7
  refine WP.bind (WP.callMC_ptrProject (projI hi₁₁ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_loadV hi₁₁ hc₁₁ hr fun m₁₂ rL₂ hc₁₂ hi₁₂ => ?_)
  simp only [StateT.run_pure]
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (wp_unlockM threadMutex rfl rfl ⟨⟩ hi₁₂ hc₁₂)))
  rintro _ G₄ m₁₃ d₄ ⟨-, -, hi₁₃⟩
  -- the event wait
  refine WP.bind (WP.callMC_ptrProject (projI hi₁₃ (k := 12) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (wp_ewait resetEvent rfl ⟨⟩ hplM hi₁₃)))
  rintro _ G₅ m₁₄ d₅ ⟨-, -, hi₁₄⟩
  -- the join of the producer, the free of the `Box`
  refine WP.bind (wp_join hi₁₄ fun _ _ m₁₅ _ hb₁₅ hcl hja => ?_)
  refine WP.pure' ?_
  refine WP.bind (wp_free hb₁₅ hcl fun m₁₆ hth => ?_)
  exact WP.pure' ⟨rfl, fun r hr hsp => hja r (hth ▸ hr) hsp⟩

/-! ## The results -/

/-- **`threadsync.handoff` gives 7 under every schedule** (every oracle `o`, every `fuel`). -/
theorem handoff_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o handoff (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 7 := by
  obtain ⟨_, _, hv, -⟩ := (proto lo prodOf).run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ) h
  exact hv

/-- **No run of `threadsync.handoff` gives an error**: no data race, no deadlock at a futex, no
panic, under every schedule. -/
theorem handoff_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o handoff (mem0 σ)).run ≠ some (.error e) :=
  (proto lo prodOf).run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (main_spec σ)

omit [Zig.Os.HasEnv] in
/-- One schedule completes: under the oracle that always picks option 0, the `std.Thread.Condition` handoff returns 7 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`), in the example OS
environment (`Os.Env.example`; the run reads no clock). -/
theorem handoff_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0)
      (@handoff ⟨Os.Env.example⟩) (mem0 σ)) = some 7 :=
  ⟨.fresh, by unroll_sched 10⟩

end Threadsync.HO
