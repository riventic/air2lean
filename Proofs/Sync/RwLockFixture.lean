import Proofs.RwRead.Walks
import Proofs.RwRead.Start
import Proofs.RwRead.Threads
import Proofs.RwRead.Stop
import ZigLean.Conc.RunResult

/-!
# `rwLockRead` and `rwLockSnapshotPair` over all schedules

`rwLockRead` and `rwLockSnapshotPair` (examples/sync/sync.zig) spawn a writer, which adds 1 two
times to a counter `n` under the write lock of an `Io.RwLock` (translated from Zig's std code; the
futex under it is the model). `rwLockRead` reads `n` under the read lock while the writer runs
and again after its join: `10 * first + last` is 2, 12 or 22 under every schedule
(`rwLockRead_spec`). `rwLockSnapshotPair` reads `n` two times under one read lock: `10 * first +
second` is 0, 11 or 22 (`snapshotPair_spec`). No schedule gives an error (`rwLockRead_safe`,
`snapshotPair_safe`): no data race on `n`, no deadlock. One schedule of each completes
(`rwLockRead_completes`, `snapshotPair_completes`, computed by the kernel).

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`) and uses only
the reader/writer lock's contract (`RwLockImpl`): this program's `Io.RwLock` is `Sync.ioRwLock`.
The protocol, its start, its thread steps and `main`'s end are once for every implementation
(`Proofs/RwRead/`); `writer` and `readShared` (`Proofs/RwRead/Walks.lean`) and both `main`s
(`rwLockRead_main`, `snapshotPair_main`) are walked by `fsym`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.RwRead Sync

namespace Sync.RwRead

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Mutex.lean`).
attribute [local irreducible] Proto.WP

/-! ## The writer -/

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

/-! ## The results of `rwLockRead` -/

/-- `main` of `rwLockRead`, walked by `fsym`: the `Shared` on its stack starts the protocol
(`inv_start`), the spawn, a read while the writer runs, the join, the read after it, the free. -/
theorem rwLockRead_main (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (rwLockRead io) QRead G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold rwLockRead
  fsym [FTriple.allocStack', inv_start (wOf := wOf), inv_spawn (wOf := wOf), readShared_run,
    inv_joins (wOf := wOf), wp_join (wOf := wOf), WP.liftMem_mul, readShared_done,
    wp_free (wOf := wOf), QRead.of_toNat]

/-- **`rwLockRead` gives 2, 12 or 22 under every schedule** (every oracle `o`, every `fuel`): the
first read sees 0, 1 or 2 increments, the read after the join sees both. -/
theorem rwLockRead_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockRead io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 2 ∨ v = .ok 12 ∨ v = .ok 22 := by
  obtain ⟨_, _, hq⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (rwLockRead_main σ io) h
  exact QRead.result hq

/-- **No run of `rwLockRead` gives an error**: no data race on `n`, no deadlock, no panic, under
every schedule. -/
theorem rwLockRead_safe (env : Env) (henv : env.spawn = .available) {σ : Placement}
    {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    e ≠ .stackOverflow →
      (Sched.run env dispatch fuel o (rwLockRead io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (rwLockRead_main σ io)

/-- One schedule completes: under the oracle that always picks option 0, the `Io.RwLock` reader
returns 2 (it reads before the writer) within fuel 1000, from `mem0` with the translation's spawn
policy. The kernel computes the run once the `zig_run` set has unfolded its path
(`docs/proof-tools.md`, concrete runs of programs with loops). -/
theorem rwLockRead_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (rwLockRead ⟨⟩) (mem0 σ)) = some 2 := by
  refine ⟨.fresh, ?_⟩
  iterate 10 (simp (config := { singlePass := true, unfoldPartialApp := true }) only [zig_run])
  decide +kernel

/-! ## The results of `rwLockSnapshotPair` -/

/-- `main` of `rwLockSnapshotPair`, walked by `fsym`: as `rwLockRead_main`, with both loads of
`n` under one read lock. -/
theorem snapshotPair_main (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (rwLockSnapshotPair io) QPair G0 { mem0 σ with current := 0 } d := by
  cases io
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold rwLockSnapshotPair
  fsym [FTriple.allocStack', inv_start (wOf := wOf), inv_spawn (wOf := wOf),
    WP.liftMem_pure (projI (wOf := wOf) _ _) rfl,
    wp_lockShared (wOf := wOf) ioRwLock rfl rfl,
    wp_loadShare (wOf := wOf),
    wp_unlockShared (wOf := wOf) ioRwLock rfl rfl,
    inv_joins (wOf := wOf), wp_join (wOf := wOf), WP.liftMem_mul,
    wp_free (wOf := wOf), QPair.of_toNat, Thr.cnt_le]

/-- **`rwLockSnapshotPair` gives 0, 11 or 22 under every schedule** (every oracle `o`, every
`fuel`): both loads are under one read lock and read one value, 0, 1 or 2 increments. -/
theorem snapshotPair_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run =
      some (.ok (v, m))) :
    v = .ok 0 ∨ v = .ok 11 ∨ v = .ok 22 := by
  obtain ⟨_, _, hq⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0
    dispatch_spec (fun _ _ _ _ _ hq => hq.2) rfl (snapshotPair_main σ io) h
  exact QPair.result hq

/-- **No run of `rwLockSnapshotPair` gives an error**: no data race on `n`, no deadlock, no
panic, under every schedule. -/
theorem snapshotPair_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {e : Error} (io : Io) :
    e ≠ .stackOverflow →
      (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (snapshotPair_main σ io)

/-- One schedule completes: under the oracle that always picks option 0, the snapshot-pair reader
returns 0 (both reads before the writer) within fuel 1000, from `mem0` with the translation's
spawn policy. The kernel computes the run once the `zig_run` set has unfolded its path
(`docs/proof-tools.md`, concrete runs of programs with loops). -/
theorem snapshotPair_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (rwLockSnapshotPair ⟨⟩) (mem0 σ)) = some 0 := by
  refine ⟨.fresh, ?_⟩
  iterate 10 (simp (config := { singlePass := true, unfoldPartialApp := true }) only [zig_run])
  decide +kernel

end Sync.RwRead
