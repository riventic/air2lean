import Proofs.RwRead.Ops
import Proofs.Sync.IoRwLock
import ZigLean.Sep.Full.AutoWP

/-!
# `writer` and `readShared` of `examples/sync/sync.zig`, under the lock's protocol

The two functions of `rwLockRead` and `rwLockSnapshotPair` that run around the reader/writer
lock, as `Proto.WP` triples over the protocol's invariant (`Proofs/RwRead/Protocol.lean`), walked
by `fsym` with the client's steps (`Proofs/RwRead/Ops.lean`) and the lock's contract
(`RwLockImpl`, at `Sync.ioRwLock`) as rules.

- `writer_spec`: the writer's two increments of `n`, each under the write lock.
- `readShared_spec`: a read of `n` under the read lock: the value is the writer's increments at
  the time of `lockSharedUncancelable` (`cnt Y`, with the threads' fact `Thr Y`: `0..2`, and `2`
  after the join).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Zig.RwRead Sync

namespace Sync.RwRead

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

/-- One run of `writer`'s loop: `io`, `lockUncancelable`, the increment of `n`, `io`, `unlock`.
Walked by `fsym` in its `WP` mode, with the protocol's steps and the lock's contract as rules. -/
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
    wp_lock (wOf := wOf) ioRwLock rfl rfl _ hp,
    wp_ownN (wOf := wOf), wp_own (wOf := wOf),
    wp_unlockN (wOf := wOf) ioRwLock rfl rfl _ _ hp,
    writer.again4]

/-- `writer`: two runs of its loop. -/
theorem writer_spec (rp : Res) (hp : rp.Plain) (t : ThreadId) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : proto.inv (upd G t (gO rp (.wr 0))) m) (hc : m.current = t) :
    proto.WP t (writer cPtr) (fun _ G' m' _ => m'.current = t ∧
      proto.inv (upd G' t (gO rp (.wr 2))) m') G m d := by
  unfold writer
  fsym [WP.loop _ _ (wrInv rp t) (fun _ => 0) (wrPost rp t) (loop4_body rp hp t)]

/-! ## `readShared` -/

/-- `readShared` by a thread at the place `y`: `io`, `lockSharedUncancelable`, the load of `n`
through the share, `io`, `unlockShared`. Its value is the writer's increments at the time of the
lock (`cnt Y`, at client parts `Y` with the threads' fact and the caller at `y`). -/
theorem readShared_spec (rp : Res) (hp : rp.Plain) (t : ThreadId) (y : Ph) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (hi : proto.inv (upd G t (gO rp y)) m) (hc : m.current = t) :
    proto.WP t (readShared cPtr) (fun v G' m' _ => m'.current = t ∧
      (∃ (Y : ThreadId → Ph) (ts : Array ThreadRec), Thr Y ts ∧ Y t = y ∧
        v = BitVec.ofNat 32 (cnt Y)) ∧
      proto.inv (upd G' t (gO rp y)) m') G m d := by
  unfold readShared
  fsym [WP.liftMem_pure (projI (wOf := wOf) _ _) rfl,
    wp_ioAt (wOf := wOf) (gO_live _ _), wp_ioAt (wOf := wOf) (gR_live _ _ _ _),
    wp_lockShared (wOf := wOf) ioRwLock rfl rfl _ hp,
    wp_loadShare (wOf := wOf),
    wp_unlockShared (wOf := wOf) ioRwLock rfl rfl _ hp]

end Sync.RwRead
