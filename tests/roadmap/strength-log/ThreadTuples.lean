import ThreadTuples.Proofs

/-!
Thread tuple migration: heap parts become full-state resources; separating unions become
`rsum`, empty parts `rnil`, ownership `FOwned`, and generated capture grants `FCapture.grant`.
The caller still proves the same disjoint split, every captured pointer's grant, and the fork
or join run. These examples retain the universal memories, thread IDs and resources.
-/

open Zig Zig.Conc Zig.Full Zig.Full.FAssn

namespace StrengthLog.ThreadTuples

example {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep child : Res} (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c child) rO m' :=
  ThreadTuples.Proofs.explicit_fork ho ht hsplit hd hf

example {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t u : ThreadId}
    (ho : FOwned own rO m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    ∀ l fc, (own u).heap l = some fc →
      (upd (upd own u rnil) t (rsum (own t) (own u)) t).heap l = some fc :=
  ThreadTuples.Proofs.worker_join ho ht hut hj

example {mode : Ptr → FTransfer} {v : BitVec 32} (first second : BitVec 32) (out other : Ptr)
    (hout : mode out = .owned (up (pts out 4 v))) :
    ¬ ∃ keep child, rnil = rsum keep child ∧ FCapture.grant mode
      (ThreadTuples.Tgt.captures (.mixedWorker (first, out, second, other))) child :=
  ThreadTuples.Proofs.unowned_output_rejected first second out other hout

end StrengthLog.ThreadTuples
