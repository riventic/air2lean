import ThreadTuples.Nonvacuity
import SpawnFailure.Nonvacuity

/-!
Strength log for the tuple-capture and failed-spawn clients. These examples retain
the full `Res` values, arbitrary rest resource, failed-assignment frame and later
successful join. The fourteen pure headers are unchanged in the client migration.
No legacy judgment or strength adapter is needed to state these obligations.
-/

open Zig Zig.Conc Zig.Full Zig.Full.FAssn

namespace StrengthLog.ThreadFixtures

example {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep child : Res} (first second : BitVec 32) (out other : Ptr)
    (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (houtputs : (up (pts out 4 (0#32)) ⋆ up (pts other 4 (0#32))) child)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c child) rO m' ∧
      ThreadTuples.Tgt.spawnInit (ThreadTuples.Proofs.protocol ThreadTuples.Proofs.mixedGrant)
        (.mixedWorker (first, out, second, other))
        { captured := .mixedWorker (first, out, second, other), privateRes := child } :=
  ThreadTuples.Proofs.mixed_fork first second out other ho ht hsplit hd houtputs hf

example {own : ThreadId → Res} {rO : Res} {m : Mem} {P : Proto Target Unit}
    {G : ThreadId → Unit} {t depth : Nat} (ho : FOwned own rO m) :
    P.WP t ((spawnOutcomeC 1 Target.worker : CM Target Unit _).run ())
      (fun result _ m' _ => result = (.error "ThreadQuotaExceeded", ()) ∧ FOwned own rO m') G m depth :=
  failedSpawnOwnership ho

example {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t first c : ThreadId}
    {depth : Nat} (hc : c ≠ 0) (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hne : first ≠ t)
    (hj : ((Thread.join first).run { m with current := t }).run = some (.ok ((), m'))) :
    (spawnOutcomeC c Target.worker : CM Target Unit _).run () depth { m with current := t } =
      CoN.leaf (some (.ok ((.error (spawnErrorAt (c - 1)), ()), { m with current := t }))) ∧
    FOwned (upd (upd own t (rsum (own t) (own first))) first rnil) rO m' :=
  refusedSecondThenJoin hc ho ht hne hj

end StrengthLog.ThreadFixtures

