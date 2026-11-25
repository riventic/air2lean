import Proofs.RwRead.Ops
import Proofs.RwRead.Start
import Proofs.RwRead.Threads
import Proofs.RwRead.Stop
import Proofs.Sync.RwLockCases
import ZigLean.Sep.Full.AutoWP
import ZigLean.Conc.RunResult

/-!
# `rwLockRead` and `rwLockSnapshotPair` over all schedules, for the Zig 0.17.1 Sync profile

`Proofs/RwRead/Walks.lean` and `Proofs/Sync/RwLockFixture.lean` for the actual Zig 0.17.1 Linux
translation (`Proofs/Sync/Gen/V0_17_1/H_6c696e7578/Gen.lean`): the same walks of `writer`,
`readShared` and both `main`s, with that translation's `Io.RwLock` contract
(`Proofs/Sync/RwLockCases.lean`). The protocol, its start, its thread steps and `main`'s end are
once for every implementation (`Proofs/RwRead/`). The four results have the public theorems'
statements word for word, over this translation's names (`assurance/theorem-list.json`: `cases`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.RwRead

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578.RwRead

open Sync.Gen.V0_17_1.H_6c696e7578

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Mutex.lean`).
attribute [local irreducible] Proto.WP

/-- The writer's argument. -/
def wOf : Tgt → Option Ptr
  | .writer p => some p
  | _ => none

/-- This program's protocol. -/
noncomputable abbrev proto : Proto Tgt Gh := Zig.RwRead.proto wOf

/-! ## `writer` -/

/-- `writer`'s loop invariant: thread `t` did `local1` increments and holds no lock. -/
def wrInv (rp : Res) (t : ThreadId) (s : writerLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  m.current = t ∧ ∃ k, proto.inv (upd G t (gO rp (.wr k))) m ∧ s.local1.toNat = k ∧ k ≤ 2

/-- `writer`'s loop ends after 2 increments. -/
def wrPost (rp : Res) (t : ThreadId) (r : writerExit × writerLocals) (G : ThreadId → Gh)
    (m : Mem) (_ : Nat) : Prop :=
  r.1 = .br3 ∧ m.current = t ∧ ∃ k, proto.inv (upd G t (gO rp (.wr k))) m ∧ k = 2

/-- One run of `writer`'s loop: `io`, `lockUncancelable`, the increment of `n`, `io`, `unlock`. -/
theorem loop4_body (rp : Res) (hp : rp.Plain) (t : ThreadId) (s : writerLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (h : wrInv rp t s G m d) :
    proto.WP t ((writer.loop4 cPtr).run s) (fun r G' m' d' =>
      if writer.again4 r.1 then wrInv rp t r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : writerLocals) => 0) s)
      else wrPost rp t r G' m' d') G m d := by
  obtain ⟨hc, k, hi, hk, hle⟩ := h
  unfold writer.loop4
  fsym [wp_tickO (wOf := wOf) hp,
    WP.liftMem_pure (projI (wOf := wOf) _ _) rfl,
    wp_ioAt (wOf := wOf) (gO_live _ _), wp_ioAt (wOf := wOf) (gW_live _ _ _),
    wp_lock (wOf := wOf) rwLock rfl rfl _ hp,
    wp_ownN (wOf := wOf), wp_own (wOf := wOf),
    wp_unlockN (wOf := wOf) rwLock rfl rfl _ _ hp,
    writer.again4]

/-- `writer`: two runs of its loop. -/
theorem writer_spec (rp : Res) (hp : rp.Plain) (t : ThreadId) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : proto.inv (upd G t (gO rp (.wr 0))) m) (hc : m.current = t) :
    proto.WP t (writer cPtr) (fun _ G' m' _ => m'.current = t ∧
      proto.inv (upd G' t (gO rp (.wr 2))) m') G m d := by
  unfold writer
  fsym [WP.loop _ _ (wrInv rp t) (fun _ => 0) (wrPost rp t) (loop4_body rp hp t)]

/-! ## `readShared` -/

/-- `readShared` by a thread at the place `y` (as `Sync.RwRead.readShared_spec`). -/
theorem readShared_spec (rp : Res) (hp : rp.Plain) (t : ThreadId) (y : Ph) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (hi : proto.inv (upd G t (gO rp y)) m) (hc : m.current = t) :
    proto.WP t (readShared cPtr) (fun v G' m' _ => m'.current = t ∧
      (∃ (Y : ThreadId → Ph) (ts : Array ThreadRec), Thr Y ts ∧ Y t = y ∧
        v = BitVec.ofNat 32 (cnt Y)) ∧
      proto.inv (upd G' t (gO rp y)) m') G m d := by
  unfold readShared
  fsym [WP.liftMem_pure (projI (wOf := wOf) _ _) rfl,
    wp_ioAt (wOf := wOf) (gO_live _ _), wp_ioAt (wOf := wOf) (gR_live _ _ _ _),
    wp_lockShared (wOf := wOf) rwLock rfl rfl _ hp,
    wp_loadShare (wOf := wOf),
    wp_unlockShared (wOf := wOf) rwLock rfl rfl _ hp]

/-! ## The writer thread -/

/-- The writer thread: `writer` on the `Shared`, then its end (`kid_end`). -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | writer p =>
    obtain ⟨hp, rp, hplain, rfl⟩ := hg
    obtain rfl : p = cPtr := Option.some.inj hp
    have hu1 : u = 1 :=
      ((thr_of hi).wr (u := u) (k := 0) (by show (G u).2.x = _; rw [hgu]; rfl)).1
    subst hu1
    have hcur : proto.inv G { m with current := 1 } := by
      obtain ⟨-, -, -, h⟩ := (fits (wOf := wOf)).m.cur 1 hi (by rw [hgu]; exact gO_live rp (.wr 0))
      exact h
    show proto.WP 1 ((fun _ => ()) <$> writer cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (writer_spec rp (Res.plain_of hplain) 1 G _ d
      (by rw [show gO rp (.wr 0) = G 1 from hgu.symm, upd_same]; exact hcur) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact kid_end (FAssn.Unshared.plain rp hplain) hi'
  | producer p => exact absurd hg.1 (by simp [wOf])
  | work p => exact absurd hg.1 (by simp [wOf])
  | semWork p => exact absurd hg.1 (by simp [wOf])

/-! ## `main`'s reads -/

/-- `main`'s read of `n` while the writer runs (`readShared_spec` at `run`): 0, 1 or 2. -/
theorem readShared_run (rp : Res) (hp : rp.Plain) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 0 (gO rp .run)) m) (hc : m.current = 0) :
    proto.WP 0 (readShared cPtr) (fun v G' m' _ => m'.current = 0 ∧ v.toNat ≤ 2 ∧
      proto.inv (upd G' 0 (gO rp .run)) m') G m d := by
  refine WP.mono ?_ (readShared_spec rp hp 0 .run G m d hi hc)
  rintro v G' m' _ ⟨hc', ⟨Y, ts, hT, -, rfl⟩, hi'⟩
  refine ⟨hc', ?_, hi'⟩
  show (BitVec.ofNat 32 (cnt Y)).toNat ≤ 2
  rw [BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) hT.cnt_le

/-- `main`'s read of `n` after its join (`readShared_spec` at `done`): 2. -/
theorem readShared_done (rp : Res) (hp : rp.Plain) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 0 (gO rp .done)) m) (hc : m.current = 0) :
    proto.WP 0 (readShared cPtr) (fun v G' m' _ => m'.current = 0 ∧ v.toNat = 2 ∧
      proto.inv (upd G' 0 (gO rp .done)) m') G m d := by
  refine WP.mono ?_ (readShared_spec rp hp 0 .done G m d hi hc)
  rintro v G' m' _ ⟨hc', ⟨Y, ts, hT, h0, rfl⟩, hi'⟩
  refine ⟨hc', ?_, hi'⟩
  show (BitVec.ofNat 32 (cnt Y)).toNat = 2
  rw [hT.done h0]
  rfl

end Sync.CaseContracts.V0_17_1.H_6c696e7578.RwRead

/-! ## The results of `rwLockRead` -/

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578.RwLockRead

open Sync.Gen.V0_17_1.H_6c696e7578
open Sync.CaseContracts.V0_17_1.H_6c696e7578.RwRead (wOf dispatch_spec readShared_run readShared_done)

/-- `main` of `rwLockRead`, walked by `fsym` (as `Sync.RwLockRead.rwLockRead_main`). -/
theorem rwLockRead_main (σ : Placement) (io : Io) (d : Nat) :
    RwRead.proto.WP 0 (rwLockRead io) QRead G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold rwLockRead
  fsym [FTriple.allocStack', inv_start (wOf := wOf), inv_spawn (wOf := wOf), readShared_run,
    inv_joins (wOf := wOf), wp_join (wOf := wOf), WP.liftMem_mul, readShared_done,
    wp_free (wOf := wOf), QRead.of_toNat]

/-- **`rwLockRead` gives 2, 12 or 22 under every schedule** (every oracle `o`, every `fuel`), in
the Zig 0.17.1 translation. -/
theorem rwLockRead_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockRead io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 2 ∨ v = .ok 12 ∨ v = .ok 22 := by
  obtain ⟨_, _, hq⟩ := RwRead.proto.run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (rwLockRead_main σ io) h
  exact QRead.result hq

/-- **No run of `rwLockRead` gives an error** in the Zig 0.17.1 translation: no data race on `n`,
no deadlock, no panic, under every schedule. -/
theorem rwLockRead_safe (env : Env) (henv : env.spawn = .available) {σ : Placement}
    {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow →
      (Sched.run env dispatch fuel o (rwLockRead io) (mem0 σ)).run ≠ some (.error e) :=
  RwRead.proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (rwLockRead_main σ io)

end Sync.CaseContracts.V0_17_1.H_6c696e7578.RwLockRead

/-! ## The results of `rwLockSnapshotPair` -/

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578.RwLockSnapshotPair

open Sync.Gen.V0_17_1.H_6c696e7578
open Sync.CaseContracts.V0_17_1.H_6c696e7578.RwRead (wOf dispatch_spec)

/-- `main` of `rwLockSnapshotPair`, walked by `fsym` (as
`Sync.RwLockSnapshotPair.snapshotPair_main`). -/
theorem snapshotPair_main (σ : Placement) (io : Io) (d : Nat) :
    RwRead.proto.WP 0 (rwLockSnapshotPair io) QPair G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold rwLockSnapshotPair
  fsym [FTriple.allocStack', inv_start (wOf := wOf), inv_spawn (wOf := wOf),
    WP.liftMem_pure (projI (wOf := wOf) _ _) rfl,
    wp_lockShared (wOf := wOf) rwLock rfl rfl,
    wp_loadShare (wOf := wOf),
    wp_unlockShared (wOf := wOf) rwLock rfl rfl,
    inv_joins (wOf := wOf), wp_join (wOf := wOf), WP.liftMem_mul,
    wp_free (wOf := wOf), QPair.of_toNat, Thr.cnt_le]

/-- **`rwLockSnapshotPair` gives 0, 11 or 22 under every schedule** (every oracle `o`, every
`fuel`), in the Zig 0.17.1 translation. -/
theorem snapshotPair_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run =
      some (.ok (v, m))) :
    v = .ok 0 ∨ v = .ok 11 ∨ v = .ok 22 := by
  obtain ⟨_, _, hq⟩ := RwRead.proto.run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (snapshotPair_main σ io) h
  exact QPair.result hq

/-- **No run of `rwLockSnapshotPair` gives an error** in the Zig 0.17.1 translation: no data
race on `n`, no deadlock, no panic, under every schedule. -/
theorem snapshotPair_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {e : Error} (io : Io) :
    e ≠ .stackOverflow →
      (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run ≠ some (.error e) :=
  RwRead.proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (snapshotPair_main σ io)

end Sync.CaseContracts.V0_17_1.H_6c696e7578.RwLockSnapshotPair
