import Proofs.Handoff.Ops
import Proofs.Sync.Cond
import Proofs.Sync.Event
import ZigLean.Conc.Unroll
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

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
  -- `io`: the library's `FLock.Fits.wp_readRest` with this protocol's obligations; `v = 7` and
  -- `ready = true`: the lock holder's step, `FLock.Fits.wp_hold`, to the producer's next place
  fsym [WP.liftMem_pure (projI (Lo := lo) (prodOf := prodOf) _ _) rfl,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_readRest rfl (by decide)
      (io_rest (a := 8) rfl (by decide)) (fun _ _ _ hu => hu.io) (io_cov rfl)
      (fun _ _ _ hu ht _ hcs => U_rec hu hcs rfl ht (by decide) (by decide)),
    wp_lockP (Lo := lo) (prodOf := prodOf) ioMutex rfl rfl ⟨⟩,
    wp_unlockP (Lo := lo) (prodOf := prodOf) ioMutex rfl rfl ⟨⟩,
    wp_signal (Lo := lo) (prodOf := prodOf) ioCond rfl ⟨⟩,
    wp_set (Lo := lo) (prodOf := prodOf) ioEvent rfl ⟨⟩,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := fun r => gH rnil r { ph := .v7 }),
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := fun r => gH rnil r { ph := .rdy }),
    U_storeHeld (Lo := lo), vOf, Ph.hasV, Ph.hasR]

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
  -- `ready`: the lock holder's step at `main`'s place (`FLock.Fits.wp_hold`); `false`: the
  -- condition wait
  fsym [WP.liftMem_pure (projI (Lo := lo) (prodOf := prodOf) _ _) rfl,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := fun r => gH rM r { ph := .run }),
    U_holdStep (Lo := lo), wp_cwait (Lo := lo) (prodOf := prodOf) ioCond rfl rfl rfl ⟨⟩ hpl,
    handoff.again24]

theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    (proto lo prodOf).WP 0 (handoff io) QM G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold handoff
  -- the `Box` (block 0, a stack block in the plain mode, which `main` keeps) and its fields'
  -- stores; the protocol's start with `main`'s part `rM` (`inv_of_box`) and the spawn; `lock`,
  -- the `ready` loop, `v` (the lock holder's step, `FLock.Fits.wp_hold`: the producer stored 7,
  -- `vOf_ready`), `unlock`, the event wait, the join of the producer, the free of the `Box`
  fsym [inv_of_box (Lo := lo) (prodOf := prodOf), inv_spawn (Lo := lo) (prodOf := prodOf),
    WP.liftMem_pure (projI (Lo := lo) (prodOf := prodOf) _ _) rfl,
    wp_lockM (Lo := lo) (prodOf := prodOf) ioMutex rfl rfl ⟨⟩,
    WP.loop _ _ (inv24 _) (fun _ => 0) (post24 _) (loop24_body _ _),
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := (fun rM r => gH rM r { ph := .run }) _),
    U_holdStep (Lo := lo), vOf_ready, wp_unlockM (Lo := lo) (prodOf := prodOf) ioMutex rfl rfl ⟨⟩,
    wp_ewait (Lo := lo) (prodOf := prodOf) ioEvent rfl ⟨⟩ _, wp_join (Lo := lo) (prodOf := prodOf),
    wp_free (Lo := lo) (prodOf := prodOf), joinedAll_of_threads]

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
