import Proofs.Sync.Proofs

/-!
# Actual generated RwLock snapshot runtime regressions

`Zig.loop` is a `partial_fixpoint`: its logical body is opaque to definitional kernel
reduction. The all-fuel/all-oracle WP/result/strict-safety proofs are separately checked
in `RwLockSnapshotPair`; these finite assertions execute its compiled production model.
They do not use `native_decide`, add axioms, or redirect the generated client/dispatcher.
The no-join fixture is explicitly a model mutation using the real writer and lock calls.
-/

open Zig Sync

private def snapshotCompleted : Bool :=
  match (Sched.run ⟨.any, .available⟩ dispatch 256 sc (rwLockSnapshotPair {}) (mem0 .fresh)).run with
  | some (.ok (.ok v, m)) =>
    (v == 0 || v == 11 || v == 22) &&
      m.threads.all (fun r => r.joined) && m.blocks[0]?.any (fun b => !b.live)
  | _ => false

/-- A model mutation of the real client's initialize/spawn/hold/read/release sequence:
only the writer join is omitted. Uses the actual exported writer and lock operations. -/
private def snapshotWithoutJoin : ConcM Tgt (BitVec 32) :=
  ((do
    let p ← allocStack 64 8
    store 8 p ({} : Io)
    store 8 (p.add 16) Sync.RwLockRead.rw0
    store 4 (p.add 56) (0 : BitVec 32)
    let spawned ← spawnC (.writer p)
    match spawned with
    | .error _ => throw .panic
    | .ok _ =>
      callC (Io_RwLock_lockSharedUncancelable (p.add 16) {})
      let first ← load (BitVec 32) 4 (p.add 56)
      let second ← load (BitVec 32) 4 (p.add 56)
      callC (Io_RwLock_unlockShared (p.add 16) {})
      free p
      let product ← Zig.mul false (10 : BitVec 32) first
      Zig.add false product second
  ) : CM Tgt Unit (BitVec 32)).run' ()

/-- Reclamation and return cannot hide an unjoined production writer. The scheduler's
actual end-of-thread lifetime guard rejects the mutation with `.illegal`. -/
private def snapshotWithoutJoinRejected : Bool :=
    match (Sched.run ⟨.any, .available⟩ dispatch 64 sc snapshotWithoutJoin (mem0 .fresh)).run with
     | some (.error .illegal) => true
     | _ => false

/-- A disjoint live caller allocation surrounds the actual production call. This finite
frame witness does not generalize the restricted block-0 all-oracle proof above. -/
private def snapshotWithSentinel : ConcM Tgt (Except ErrName (BitVec 32) × BitVec 32) := do
  let sentinel ← alloc .heap 4 4
  store 4 sentinel (73 : BitVec 32)
  let result ← rwLockSnapshotPair {}
  let observed ← load (BitVec 32) 4 sentinel
  free sentinel
  pure (result, observed)

/-- The actual client preserves the caller's literal sentinel; both allocations are freed
and all threads joined at completion. Never accept a fuel-exhausted or errored witness. -/
private def snapshotPreservesSentinel : Bool :=
    match (Sched.run ⟨.any, .available⟩ dispatch 256 sc snapshotWithSentinel (mem0 .fresh)).run with
     | some (.ok ((.ok v, sentinel), m)) =>
       (v == 0 || v == 11 || v == 22) && sentinel == 73 &&
         m.threads.all (fun r => r.joined) &&
         m.blocks[0]?.any (fun b => !b.live) && m.blocks[1]?.any (fun b => !b.live)
     | _ => false

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  require snapshotCompleted "snapshot client did not complete with 0/11/22, joined tasks and freed Shared"
  require snapshotPreservesSentinel "snapshot client did not preserve sentinel 73 and reclaim both allocations"
  require snapshotWithoutJoinRejected "omitted writer join did not produce the scheduler lifetime error illegal"
  IO.println "Sync snapshot runtime regressions passed"
