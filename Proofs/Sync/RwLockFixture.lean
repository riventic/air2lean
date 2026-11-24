import Proofs.RwRead.Walks
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
The protocol, its steps and `main`'s end are once for every implementation (`Proofs/RwRead/`);
`writer` and `readShared` are walked by `fsym` (`Proofs/RwRead/Walks.lean`).

The results take the pieces that are proved in other files as premises, each named at its
theorem: the writer's end (`hend`), and `main`'s walk of each program (`hmain`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.RwRead Sync

namespace Sync.RwRead

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/Mutex.lean`).
attribute [local irreducible] Proto.WP

/-! ## The writer -/

/-- The writer thread: `writer` on the `Shared`, then its end. `hend` is the writer's end: after
its two increments, out of the lock's code, it has a last ghost value that satisfies the
protocol's `fin`. -/
theorem dispatch_spec
    (hend : ∀ (G : ThreadId → Gh) (m : Mem) (rp : Res), plain rp →
      proto.inv (upd G 1 (gO rp (.wr 2))) m → ∃ g, proto.inv (upd G 1 g) m ∧ proto.fin g)
    (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
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
      obtain ⟨-, -, -, h⟩ := (fits (wOf := wOf)).m.cur 1 hi (by rw [hgu]; exact gO_live _ _)
      exact h
    show proto.WP 1 ((fun _ => ()) <$> writer cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (writer_spec rp (Res.plain_of hplain) 1 G _ d
      (by rw [show gO rp (.wr 0) = G 1 from hgu.symm, upd_same]; exact hcur) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    obtain ⟨g, hig, hfin⟩ := hend G' m' rp hplain hi'
    have hq : ∃ g, proto.inv (upd G' 1 g) m' ∧ proto.fin g ∧
        (proto.strict = true → joinedAll 1 m') :=
      ⟨g, hig, hfin, fun _ => joinedAll_of_main (thr_of hig).spawner0 (by decide)⟩
    exact hq
  | producer p => exact absurd hg.1 (by simp [wOf])
  | work p => exact absurd hg.1 (by simp [wOf])
  | semWork p => exact absurd hg.1 (by simp [wOf])

/-! ## The results of `rwLockRead` -/

/-- **`rwLockRead` gives 2, 12 or 22 under every schedule** (every oracle `o`, every `fuel`): the
first read sees 0, 1 or 2 increments, the read after the join sees both. -/
theorem rwLockRead_spec {G0 : ThreadId → Gh}
    (hend : ∀ (G : ThreadId → Gh) (m : Mem) (rp : Res), plain rp →
      proto.inv (upd G 1 (gO rp (.wr 2))) m → ∃ g, proto.inv (upd G 1 g) m ∧ proto.fin g)
    (hmain : ∀ (σ : Placement) (io : Io) (d : Nat),
      proto.WP 0 (rwLockRead io) QRead G0 { mem0 σ with current := 0 } d)
    (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockRead io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 2 ∨ v = .ok 12 ∨ v = .ok 22 := by
  obtain ⟨_, _, hq⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0
    (dispatch_spec hend) (fun _ _ _ _ _ hq => hq.2) rfl (hmain σ io) h
  exact QRead.result hq

/-- **No run of `rwLockRead` gives an error**: no data race on `n`, no deadlock, no panic, under
every schedule. -/
theorem rwLockRead_safe {G0 : ThreadId → Gh}
    (hend : ∀ (G : ThreadId → Gh) (m : Mem) (rp : Res), plain rp →
      proto.inv (upd G 1 (gO rp (.wr 2))) m → ∃ g, proto.inv (upd G 1 g) m ∧ proto.fin g)
    (hmain : ∀ (σ : Placement) (io : Io) (d : Nat),
      proto.WP 0 (rwLockRead io) QRead G0 { mem0 σ with current := 0 } d)
    (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {e : Error} (io : Io) :
    e ≠ .stackOverflow →
      (Sched.run env dispatch fuel o (rwLockRead io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl (dispatch_spec hend)
    (fun _ _ _ _ hq => hq.2) rfl (hmain σ io)

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

/-- **`rwLockSnapshotPair` gives 0, 11 or 22 under every schedule** (every oracle `o`, every
`fuel`): both loads are under one read lock and read one value, 0, 1 or 2 increments. -/
theorem snapshotPair_spec {G0 : ThreadId → Gh}
    (hend : ∀ (G : ThreadId → Gh) (m : Mem) (rp : Res), plain rp →
      proto.inv (upd G 1 (gO rp (.wr 2))) m → ∃ g, proto.inv (upd G 1 g) m ∧ proto.fin g)
    (hmain : ∀ (σ : Placement) (io : Io) (d : Nat),
      proto.WP 0 (rwLockSnapshotPair io) QPair G0 { mem0 σ with current := 0 } d)
    (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {v : Except ErrName (BitVec 32)} {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run =
      some (.ok (v, m))) :
    v = .ok 0 ∨ v = .ok 11 ∨ v = .ok 22 := by
  obtain ⟨_, _, hq⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0
    (dispatch_spec hend) (fun _ _ _ _ _ hq => hq.2) rfl (hmain σ io) h
  exact QPair.result hq

/-- **No run of `rwLockSnapshotPair` gives an error**: no data race on `n`, no deadlock, no
panic, under every schedule. -/
theorem snapshotPair_safe {G0 : ThreadId → Gh}
    (hend : ∀ (G : ThreadId → Gh) (m : Mem) (rp : Res), plain rp →
      proto.inv (upd G 1 (gO rp (.wr 2))) m → ∃ g, proto.inv (upd G 1 g) m ∧ proto.fin g)
    (hmain : ∀ (σ : Placement) (io : Io) (d : Nat),
      proto.WP 0 (rwLockSnapshotPair io) QPair G0 { mem0 σ with current := 0 } d)
    (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat}
    {e : Error} (io : Io) :
    e ≠ .stackOverflow →
      (Sched.run env dispatch fuel o (rwLockSnapshotPair io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl (dispatch_spec hend)
    (fun _ _ _ _ hq => hq.2) rfl (hmain σ io)

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
