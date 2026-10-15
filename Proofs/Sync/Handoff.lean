import Proofs.Handoff.Ops
import Proofs.Sync.Cond
import Proofs.Sync.Event
import ZigLean.Conc.Unroll
import ZigLean.Sep.Full.Auto

/-!
# `handoff` over all schedules

`handoff` spawns a producer. The producer sets `v = 7` and `ready = true` under an `Io.Mutex`,
signals an `Io.Condition` and sets an `Io.Event`. `main` waits on the condition until `ready`,
reads `v`, waits on the event and joins the producer. All three sync objects are translated from
Zig's std code (0.16.0; the 0.17.0 translation of this program is the same code); the futex under
them is the model. The result is 7 under every schedule (`handoff_spec`), and no schedule gives an
error (`handoff_safe`): no data race, no deadlock at a futex, no `unreachable`.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`) and uses only
the contracts of the sync objects (`MutexImpl`, `CondImpl`, `EventImpl`): this program's
`Io.Mutex`, `Io.Condition` and `Io.Event` are `Sync.ioMutex`, `Sync.ioCond` and `Sync.ioEvent`.
The protocol and its steps are once for every version (`Proofs/Handoff/`); this file gives the
`Box`'s layout (`lo`: `io` at 0, the mutex at 16, the condition's state and epoch at 20 and 24,
the event at 28, `v` at 32, `ready` at 36) and walks `main` and the producer of the generated code.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Handoff Sync

namespace Sync.Handoff

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- The `Box`'s layout (module doc). -/
def lo : Layout where
  size := 40
  align := 8
  io := 16
  mo := 16
  so := 20
  vo := 28
  xo := 32
  ro := 36
  c := 2
  c_ok := by decide
  ok := by decide

/-- The producer's argument. -/
def prodOf : Tgt → Option Ptr
  | .producer p => some p
  | _ => none

/-! ## The producer -/

theorem producer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : (proto lo prodOf).inv (upd G 1 (gO rnil { ph := .lk })) m) (hc : m.current = 1) :
    (proto lo prodOf).WP 1 (producer bPtr) (fun _ G' m' _ => m'.current = 1 ∧
      (proto lo prodOf).inv (upd G' 1 (⟨.gone, rnil, rnil⟩, { ph := .fin })) m') G m d := by
  unfold producer
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  -- `lock`
  refine WP.bind (WP.callMC_ptrProject (projI hi (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io (a := 8) rfl (by decide) hi hc (live_t hi nofun) fun m₁ hc₁ _ hi₁ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (wp_lockP ioMutex rfl rfl ⟨⟩ hi₁)))
  rintro _ G₂ m₂ d₂ ⟨-, hc₂, rL, hi₂⟩
  -- `v = 7`, `ready = true`
  refine WP.bind (WP.callMC_ptrProject (projI hi₂ (k := 32) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_storeV hi₂ hc₂ fun m₃ rL₃ hc₃ hi₃ => ?_)
  refine WP.bind (WP.callMC_ptrProject (projI hi₃ (k := 36) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_storeR hi₃ hc₃ fun m₄ rL₄ hc₄ hi₄ => ?_)
  -- `unlock`
  refine WP.bind (WP.callMC_ptrProject (projI hi₄ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io (a := 8) rfl (by decide) hi₄ hc₄ (live_t hi₄ nofun) fun m₅ hc₅ _ hi₅ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (wp_unlockP ioMutex rfl rfl ⟨⟩ hi₅ hc₅)))
  rintro _ G₃ m₆ d₃ ⟨-, hc₆, hi₆⟩
  -- `signal`
  refine WP.bind (WP.callMC_ptrProject (projI hi₆ (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io (a := 8) rfl (by decide) hi₆ hc₆ (live_t hi₆ nofun) fun m₇ hc₇ _ hi₇ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (wp_signal ioCond rfl ⟨⟩ hi₇)))
  rintro _ G₄ m₈ d₄ ⟨-, hc₈, hi₈⟩
  -- `set`
  refine WP.bind (WP.callMC_ptrProject (projI hi₈ (k := 28) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io (a := 8) rfl (by decide) hi₈ hc₈ (live_t hi₈ nofun) fun m₉ hc₉ _ hi₉ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (wp_set ioEvent rfl ⟨⟩ hi₉)))
  rintro _ G₅ m₁₀ d₅ ⟨-, hc₁₀, hi₁₀⟩
  refine WP.pure' ?_
  exact WP.pure' ⟨hc₁₀, hi₁₀⟩

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
    show (proto lo prodOf).WP 1 ((fun _ => ()) <$> producer bPtr) _ G _ d
    refine WP.map (WP.mono ?_ (producer_spec G _ d
      (by rw [show gO rnil { ph := .lk } = G 1 from hgu.symm, upd_same]
          exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact qkid hi'
  | work p => exact absurd hg.1 (by simp [prodOf])
  | writer p => exact absurd hg.1 (by simp [prodOf])
  | semWork p => exact absurd hg.1 (by simp [prodOf])

/-! ## `main` -/

/-- The `ready` loop's invariant: `main` holds the mutex at `run`. -/
def inv24 (rM : Res) (_ : handoffLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = 0 ∧ ∃ rL, (proto lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m

/-- The `ready` loop ends: `main` read `ready = true`. -/
def post24 (rM : Res) (r : handoffExit × handoffLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  r.1 = .br23 ∧ m.current = 0 ∧ ∃ rL, (proto lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m ∧
    (G 1).2.ph.hasR = true

theorem loop24_body (rM : Res) (hpl : rM.Plain) (s : handoffLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv24 rM s G m d) :
    (proto lo prodOf).WP 0 ((handoff.loop24 ⟨⟩ bPtr).run s) (fun r G' m' d' =>
      if handoff.again24 r.1 then inv24 rM r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : handoffLocals) => 0) s)
      else post24 rM r G' m' d') G m d := by
  obtain ⟨hc, rL, hi⟩ := h
  unfold handoff.loop24
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  refine WP.bind (WP.bind (WP.callMC_ptrProject (projI hi (k := 36) (by decide)) ?_))
  dsimp only
  refine WP.bind (wp_loadR hi hc fun m' rQ hc' hi' => ?_)
  cases hr : (G 1).2.ph.hasR
  · -- `ready = false`: the condition wait
    simp only [Bool.not_false, ↓reduceIte, StateT.run_bind]
    refine WP.bind (WP.callMC_ptrProject (projI hi' (k := 20) (by decide)) ?_)
    refine WP.bind (WP.callMC_ptrProject (projI hi' (k := 16) (by decide)) ?_)
    dsimp only
    refine WP.bind (WP.callC (WP.mono ?_ (wp_cwait ioCond rfl rfl rfl ⟨⟩ hpl hi' hc' hr)))
    rintro _ G₁ m₁ d₁ ⟨hd₁, hc₁, rL₁, hi₁⟩
    simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [handoff.again24, ↓reduceIte]
    exact ⟨⟨hc₁, rL₁, hi₁⟩, .inl hd₁⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [handoff.again24, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc', rQ, hi', hr⟩

/-- The initial mutex and condition. -/
def mutex0 : Io_Mutex := { state := { raw := Io_Mutex_State.unlocked } }
def cond0 : Io_Condition :=
  { state := { raw := (Packed.ofBits (0 : BitVec 32) : Io_Condition_State) }, epoch := { raw := 0 } }

theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    (proto lo prodOf).WP 0 (handoff io) QM G0 { mem0 σ with current := 0 } d := by
  cases io
  unfold handoff
  have ht0 : ({ mem0 σ with current := 0 } : Mem).threads = #[{ spawner := 0, joined := true }] :=
    rfl
  -- the `Box`: block 0, a stack block in the plain mode, which `main` keeps
  refine WP.bind (WP.liftMem_fownedS (by fsym : FTTriple plain _ _)
    (FOwned.start0_plain σ) rfl (by rw [ht0]; decide) (by rw [plainOwn_zero]; exact plain_intro)
    fun s1 m₁ r₁ _ hr₁ ho₁ hq₁ hs₁ => ?_)
  obtain ⟨rfl, hm₁e⟩ := alloc_ok hr₁
  obtain ⟨A, b, hq₁⟩ := hq₁
  obtain ⟨⟨hpb, -, hA8⟩, F₁⟩ := Full.sep_lift.mp hq₁
  obtain rfl : b = 0 := by cases hpb; rfl
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = bPtr from rfl]
    at F₁ ⊢
  have hc₁ : m₁.current = 0 := hs₁.current
  have ht₁ : m₁.threads = #[{ spawner := 0, joined := true }] := hs₁.threads.trans ht0
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `io`
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := bPtr) (A := A) (S := 40)
    (K := .stack) (k := 0) (a := 8) (⟨⟩ : Io) rfl rfl (by decide) (by decide)
    (by simp [bPtr]; omega) (by decide)).frame ho₁ hc₁ (by rw [ht₁]; decide)
    F₁ fun _ m₂ r₂ _ hr₂ ho₂ F₂ hs₂ => ?_)
  simp only [plainOwn, upd_upd] at ho₂
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  have ht₂ : m₂.threads = #[{ spawner := 0, joined := true }] := hs₂.threads.trans ht₁
  -- the mutex
  refine WP.bind (WP.callMC_ptrProject (projO ho₂ (by rw [ht₂]; decide)
    F₂ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt' (p := bPtr) (A := A) (S := 40)
    (K := .stack) (k := 16) (a := 4) mutex0 (by decide +kernel) rfl rfl (by decide)
    (by decide +kernel) (by simp [bPtr]; omega) (by decide)).frame ho₂ hc₂ (by rw [ht₂]; decide)
    F₂ fun _ m₃ r₃ _ hr₃ ho₃ F₃ hs₃ => ?_)
  rw [upd_upd] at ho₃
  have hc₃ : m₃.current = 0 := hs₃.current.trans hc₂
  have ht₃ : m₃.threads = #[{ spawner := 0, joined := true }] := hs₃.threads.trans ht₂
  -- the condition
  refine WP.bind (WP.callMC_ptrProject (projO ho₃ (by rw [ht₃]; decide)
    F₃ (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt' (p := bPtr) (A := A) (S := 40)
    (K := .stack) (k := 20) (a := 4) cond0 (by decide +kernel) rfl rfl (by decide)
    (by decide +kernel) (by simp [bPtr]; omega) (by decide)).frame ho₃ hc₃ (by rw [ht₃]; decide)
    F₃ fun _ m₄ r₄ _ hr₄ ho₄ F₄ hs₄ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans hc₃
  have ht₄ : m₄.threads = #[{ spawner := 0, joined := true }] := hs₄.threads.trans ht₃
  -- `ready`
  refine WP.bind (WP.callMC_ptrProject (projO ho₄ (by rw [ht₄]; decide)
    F₄ (k := 36) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := bPtr) (A := A) (S := 40)
    (K := .stack) (k := 36) (a := 1) false rfl rfl (by decide) (by decide +kernel)
    (Nat.mod_one _) (by decide)).frame ho₄ hc₄ (by rw [ht₄]; decide)
    F₄ fun _ m₅ r₅ _ hr₅ ho₅ F₅ hs₅ => ?_)
  rw [upd_upd] at ho₅
  have hc₅ : m₅.current = 0 := hs₅.current.trans hc₄
  have ht₅ : m₅.threads = #[{ spawner := 0, joined := true }] := hs₅.threads.trans ht₄
  -- the event
  refine WP.bind (WP.callMC_ptrProject (projO ho₅ (by rw [ht₅]; decide)
    F₅ (k := 28) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt' (p := bPtr) (A := A) (S := 40)
    (K := .stack) (k := 28) (a := 4) Io_Event.unset (by decide +kernel) rfl rfl (by decide)
    (by decide +kernel) (by simp [bPtr]; omega) (by decide)).frame ho₅ hc₅ (by rw [ht₅]; decide)
    F₅ fun _ m₆ r₆ _ hr₆ ho₆ F₆ hs₆ => ?_)
  rw [upd_upd] at ho₆
  have hc₆ : m₆.current = 0 := hs₆.current.trans hc₅
  have ht₆ : m₆.threads = #[{ spawner := 0, joined := true }] := hs₆.threads.trans ht₅
  -- `v`
  refine WP.bind (WP.callMC_ptrProject (projO ho₆ (by rw [ht₆]; decide)
    F₆ (k := 32) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callMC_fownedS (FTTriple.storeAt (p := bPtr) (A := A) (S := 40)
    (K := .stack) (k := 32) (a := 4) (0 : BitVec 32) rfl rfl (by decide) (by decide +kernel)
    (by simp [bPtr]; omega) (by decide)).frame ho₆ hc₆ (by rw [ht₆]; decide)
    F₆ fun _ m₇ r₇ _ hr₇ ho₇ F₇ hs₇ => ?_)
  rw [upd_upd] at ho₇
  have hc₇ : m₇.current = 0 := hs₇.current.trans hc₆
  have ht₇ : m₇.threads = #[{ spawner := 0, joined := true }] := hs₇.threads.trans ht₆
  have hat₇ : m₇.atomics = #[] := by
    rw [store_atomics hr₇, store_atomics hr₆, store_atomics hr₅, store_atomics hr₄,
      store_atomics hr₃, store_atomics hr₂, hm₁e]
    rfl
  have hq₇ : m₇.waiters = #[] := by
    rw [hs₇.waiters, hs₆.waiters, hs₅.waiters, hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]
    rfl
  obtain ⟨rM, hplM, hi₀⟩ := inv_of_box (Lo := lo) (prodOf := prodOf) ho₇ F₇ (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun _ => by decide +kernel) hA8 ht₇ hat₇ hq₇
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gO rM { ph := .pre }, hi₀, fun G₁ m₈ hg₁ hi₈ =>
    ⟨gO rnil { ph := .lk }, ⟨rfl, rfl⟩, fun child m₉ hf => ?_⟩⟩)
  obtain ⟨rfl, hi₉⟩ := inv_spawn hi₈ hg₁ hf
  dsimp only
  simp only [StateT.run_bind]
  -- `lock`
  refine WP.bind (WP.callMC_ptrProject (projI hi₉ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (wp_lockM ioMutex rfl rfl ⟨⟩ hi₉)))
  rintro _ G₂ m₁₀ d₂ ⟨-, hc₁₀, rL, hi₁₀⟩
  -- the `ready` loop
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv24 rM) (fun _ => 0) (post24 rM) (loop24_body rM hplM) _
    G₂ m₁₀ d₂ ⟨hc₁₀, rL, hi₁₀⟩))
  rintro ⟨e, s'⟩ G₃ m₁₁ d₃ ⟨rfl, hc₁₁, rL₁, hi₁₁, hr⟩
  dsimp only
  simp only [StateT.run_bind]
  -- `v`: the producer stored 7
  refine WP.bind (WP.callMC_ptrProject (projI hi₁₁ (k := 32) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_loadV hi₁₁ hc₁₁ hr fun m₁₂ rL₂ hc₁₂ hi₁₂ => ?_)
  -- `unlock`
  refine WP.bind (WP.callMC_ptrProject (projI hi₁₂ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (wp_unlockM ioMutex rfl rfl ⟨⟩ hi₁₂ hc₁₂)))
  rintro _ G₄ m₁₃ d₄ ⟨-, -, hi₁₃⟩
  -- the event wait
  refine WP.bind (WP.callMC_ptrProject (projI hi₁₃ (k := 28) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (wp_ewait ioEvent rfl ⟨⟩ hplM hi₁₃)))
  rintro _ G₅ m₁₄ d₅ ⟨-, -, hi₁₄⟩
  -- the join of the producer, the free of the `Box`
  refine WP.bind (wp_join hi₁₄ fun _ _ m₁₅ _ hb₁₅ hcl hja => ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  refine WP.bind (wp_free hb₁₅ hcl fun m₁₆ hth => ?_)
  exact WP.pure' ⟨rfl, fun r hr hsp => hja r (hth ▸ hr) hsp⟩

/-! ## The results -/

/-- **`handoff` gives 7 under every schedule** (every oracle `o`, every `fuel`). -/
theorem handoff_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env dispatch fuel o (handoff io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 7 := by
  obtain ⟨_, _, hv, -⟩ := (proto lo prodOf).run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- **No run of `handoff` gives an error**: no data race, no deadlock at a futex, no
`unreachable`, under every schedule. -/
theorem handoff_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (handoff io) (mem0 σ)).run ≠ some (.error e) :=
  (proto lo prodOf).run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the `Io.Condition` handoff returns 7 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem handoff_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (handoff ⟨⟩) (mem0 σ)) = some 7 :=
  ⟨.fresh, by unroll_sched 10⟩

end Sync.Handoff
