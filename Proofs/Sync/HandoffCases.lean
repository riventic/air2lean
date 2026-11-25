import Proofs.Handoff.Ops
import Proofs.Sync.CondCases
import Proofs.Sync.EventCases
import ZigLean.Conc.RunResult
import ZigLean.Sep.Full.AutoWP
import ZigLean.Sep.Full.LockSteps

/-!
# `handoff` over all schedules, for the Zig 0.17.1 Sync profile

`Proofs/Sync/Handoff.lean` for the actual Zig 0.17.1 Linux translation
(`Proofs/Sync/Gen/V0_17_1/H_6c696e7578/Gen.lean`): the same layout and the same walks of `main`
and the producer, with that translation's `Io.Mutex`, `Io.Condition` and `Io.Event` contracts
(`Proofs/Sync/MutexCases.lean`, `CondCases.lean`, `EventCases.lean`). The protocol and its steps
are once for every version (`Proofs/Handoff/`). `handoff_spec` and `handoff_safe` have the
public theorems' statements word for word, over this translation's names
(`assurance/theorem-list.json`: `cases`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.Handoff

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578.Handoff

open Sync.Gen.V0_17_1.H_6c696e7578

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- The `Box`'s layout (`Sync.Handoff.lo`). -/
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
  fits := by decide

/-- The producer's argument. -/
def prodOf : Tgt → Option Ptr
  | .producer p => some p
  | _ => none

/-! ## The producer -/

theorem producer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) {rp : Res} (hp : rp.Plain)
    (hi : (proto lo prodOf).inv (upd G 1 (gO rp { ph := .lk })) m) (hc : m.current = 1) :
    (proto lo prodOf).WP 1 (producer bPtr) (fun _ G' m' _ => m'.current = 1 ∧
      (proto lo prodOf).inv (upd G' 1 (⟨.gone, rp, rnil⟩, { ph := .fin })) m') G m d := by
  unfold producer
  fsym [WP.liftMem_pure (projI (Lo := lo) (prodOf := prodOf) _ _) rfl,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_tick_plain,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_readRest rfl (by decide)
      (io_rest (a := 8) rfl (by decide)) (fun _ _ _ hu => hu.io) (io_cov rfl)
      (fun _ _ _ hu ht _ hcs => U_rec hu hcs rfl ht (by decide) (by decide)),
    wp_lockP (Lo := lo) (prodOf := prodOf) mutex rfl rfl ⟨⟩ hp,
    wp_unlockP (Lo := lo) (prodOf := prodOf) mutex rfl rfl ⟨⟩,
    wp_signal (Lo := lo) (prodOf := prodOf) cond rfl ⟨⟩ hp,
    wp_set (Lo := lo) (prodOf := prodOf) event rfl ⟨⟩ hp,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := fun r => gH rp r { ph := .v7 }),
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := fun r => gH rp r { ph := .rdy }),
    U_storeHeld (Lo := lo), vOf, Ph.hasV, Ph.hasR]

/-- The producer: its code, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : (proto lo prodOf).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g)
    (hi : (proto lo prodOf).inv G m) :
    (proto lo prodOf).WP u (dispatch tgt) ((proto lo prodOf).QKid u) G { m with current := u } d := by
  cases tgt with
  | producer p =>
    obtain ⟨hp, rp, hpP, rfl⟩ := hg
    obtain rfl : p = bPtr := Option.some.inj hp
    have hu1 : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      exact hU.shape.one (u := u) (by show (G u).2.ph.isProd = true; rw [hgu]; rfl)
    subst hu1
    show (proto lo prodOf).WP 1 ((fun _ => ()) <$> producer bPtr) _ G _ d
    refine WP.map (WP.mono ?_ (producer_spec G _ d (Res.plain_of hpP)
      (by rw [show gO rp { ph := .lk } = G 1 from hgu.symm, upd_same]
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
  fsym [WP.liftMem_pure (projI (Lo := lo) (prodOf := prodOf) _ _) rfl,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_tick_plain,
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := fun r => gH rM r { ph := .run }),
    U_holdStep (Lo := lo), wp_cwait (Lo := lo) (prodOf := prodOf) cond rfl rfl rfl ⟨⟩ hpl,
    handoff.again24]

theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    (proto lo prodOf).WP 0 (handoff io) QM G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold handoff
  fsym [inv_of_box (Lo := lo) (prodOf := prodOf), inv_spawn (Lo := lo) (prodOf := prodOf),
    WP.liftMem_pure (projI (Lo := lo) (prodOf := prodOf) _ _) rfl,
    wp_lockM (Lo := lo) (prodOf := prodOf) mutex rfl rfl ⟨⟩ _,
    WP.loop _ _ (inv24 _) (fun _ => 0) (post24 _) (loop24_body _ _),
    (fitsL (Lo := lo) (prodOf := prodOf)).wp_hold (g' := (fun rM r => gH rM r { ph := .run }) _),
    U_holdStep (Lo := lo), vOf_ready, wp_unlockM (Lo := lo) (prodOf := prodOf) mutex rfl rfl ⟨⟩,
    wp_ewait (Lo := lo) (prodOf := prodOf) event rfl ⟨⟩ _, wp_join (Lo := lo) (prodOf := prodOf),
    wp_free (Lo := lo) (prodOf := prodOf), joinedAll_of_threads]

/-! ## The results -/

/-- **`handoff` gives 7 under every schedule** (every oracle `o`, every `fuel`), in the Zig 0.17.1
translation. -/
theorem handoff_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env dispatch fuel o (handoff io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 7 := by
  obtain ⟨_, _, hv, -⟩ := (proto lo prodOf).run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- **No run of `handoff` gives an error** in the Zig 0.17.1 translation: no data race, no
deadlock at a futex, no `unreachable`, under every schedule. -/
theorem handoff_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (handoff io) (mem0 σ)).run ≠ some (.error e) :=
  (proto lo prodOf).run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

end Sync.CaseContracts.V0_17_1.H_6c696e7578.Handoff
