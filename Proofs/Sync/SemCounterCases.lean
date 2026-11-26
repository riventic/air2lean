import Proofs.SemCounter.Start
import Proofs.Sync.SemCases
import ZigLean.Sep.Full.AutoWP
import ZigLean.Conc.RunResult

/-!
# `semaphoreCounter` over all schedules, for the Zig 0.17.1 Sync profile

`Proofs/Sync/SemCounter.lean` for the actual Zig 0.17.1 Linux translation
(`Proofs/Sync/Gen/V0_17_1/H_6c696e7578/Gen.lean`): the same walks of `semWork` and `main`, with
that translation's `Io.Semaphore` contract (`Proofs/Sync/SemCases.lean`). The protocol, its steps
and `main`'s start and end are once for every implementation (`Proofs/SemCounter/`).
`semaphoreCounter_spec` and `semaphoreCounter_safe` have the public theorems' statements word for
word, over this translation's names (`assurance/theorem-list.json`: `cases`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.SemCounter

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578.SemCounter

open Sync.Gen.V0_17_1.H_6c696e7578

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Mutex.lean`).
attribute [local irreducible] Proto.WP

/-- The kid's argument. -/
def semOf : Tgt → Option Ptr
  | .semWork p => some p
  | _ => none

/-- This program's protocol. -/
abbrev proto : Proto Tgt Gh := Zig.SemCounter.proto semOf

/-! ## `semWork` -/

/-- `semWork`'s loop invariant: thread `t` did `local1` increments and has no permit. -/
def workInv (rp : Res) (t : ThreadId) (s : semWorkLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  m.current = t ∧ ∃ k, proto.inv (upd G t (gW rp k false 0)) m ∧ s.local1.toNat = k ∧ k ≤ 2

/-- `semWork`'s loop ends after 2 increments. -/
def workPost (rp : Res) (t : ThreadId) (r : semWorkExit × semWorkLocals) (G : ThreadId → Gh)
    (m : Mem) (_ : Nat) : Prop :=
  r.1 = .br3 ∧ m.current = t ∧ ∃ k, proto.inv (upd G t (gW rp k false 0)) m ∧ k = 2

/-- One run of `semWork`'s loop: `io`, `wait`, the increment of `n`, `io`, `post`. -/
theorem loop4_body (rp : Res) (hp : rp.Plain) (t : ThreadId) (s : semWorkLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (h : workInv rp t s G m d) :
    proto.WP t ((semWork.loop4 cPtr).run s) (fun r G' m' d' =>
      if semWork.again4 r.1 then workInv rp t r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : semWorkLocals) => 0) s)
      else workPost rp t r G' m' d') G m d := by
  obtain ⟨hc, k, hi, hk, hle⟩ := h
  unfold semWork.loop4
  fsym [(fits (semOf := semOf)).wp_tick_plain,
    WP.liftMem_pure (projI (semOf := semOf) _ _) rfl,
    (fits (semOf := semOf)).wp_readRest rfl (by decide) io_rest (fun _ _ _ hu => hu.um.io) io_cov
      (fun _ _ _ hu ht _ hcs => U_rec hu hcs rfl ht (Nat.le_refl _)),
    wp_wait (semOf := semOf) sem rfl rfl _ _ hp,
    wp_ownN (semOf := semOf), wp_own (semOf := semOf), hold_le (semOf := semOf),
    wp_postN (semOf := semOf) sem rfl rfl _ _ hp,
    semWork.again4]

/-- `semWork`: two runs of its loop. -/
theorem semWork_spec (rp : Res) (hp : rp.Plain) (t : ThreadId) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : proto.inv (upd G t (gW rp 0 false 0)) m) (hc : m.current = t) :
    proto.WP t (semWork cPtr) (fun _ G' m' _ => m'.current = t ∧
      proto.inv (upd G' t (gW rp 2 false 0)) m') G m d := by
  unfold semWork
  fsym [WP.loop _ _ (workInv rp t) (fun _ => 0) (workPost rp t) (loop4_body rp hp t)]

/-- The kid: `semWork` on the `SemCounter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | semWork p =>
    obtain ⟨hp, rp, hplain, rfl⟩ := hg
    obtain rfl : p = cPtr := Option.some.inj hp
    have hu1 : u = 1 := by
      obtain ⟨rX, -, hU⟩ := id hi
      have := (hU.um.shape.lt (u := u) (k := 0) (b := false) (s := 0)
        (by show (G u).2.ph = _; rw [hgu])).1
      unfold ThreadId at *; omega
    subst hu1
    show proto.WP 1 ((fun _ => ()) <$> semWork cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (semWork_spec rp (Res.plain_of hplain) 1 G _ d
      (by rw [show gW rp 0 false 0 = G 1 from hgu.symm, upd_same]
          exact inv_cur 1 hi (by rw [hgu]; nofun)) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact qkid (FAssn.Unshared.plain rp hplain) hi'
  | producer p => exact absurd hg.1 (by simp [semOf])
  | work p => exact absurd hg.1 (by simp [semOf])
  | writer p => exact absurd hg.1 (by simp [semOf])

/-! ## `main` -/

/-- `main`: the `SemCounter`'s start, the spawn, `semWork`, the join, the load of `n` (4) and the
free. -/
theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (semaphoreCounter io) QM G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold semaphoreCounter
  fsym [FTriple.allocStack', inv_start (semOf := semOf), inv_spawn (semOf := semOf), semWork_spec,
    inv_end (semOf := semOf), wp_join (semOf := semOf), WP.liftMem_pure (proj _ _) rfl,
    wp_free (semOf := semOf), joinedAll_of_threads]

/-! ## The results -/

/-- **`semaphoreCounter` gives 4 under every schedule** (every oracle `o`, every `fuel`), in the
Zig 0.17.1 translation. -/
theorem semaphoreCounter_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)}
    {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (semaphoreCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 4 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- **No run of `semaphoreCounter` gives an error** in the Zig 0.17.1 translation: no data race
on `n`, no deadlock, no panic, under every schedule. -/
theorem semaphoreCounter_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o (semaphoreCounter io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

end Sync.CaseContracts.V0_17_1.H_6c696e7578.SemCounter
