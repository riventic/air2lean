import Runtime

/-!
Spawn failure migration: the caller's arbitrary heap ownership is replaced by arbitrary
full-state ownership. Failure still preserves every caller resource; the join still returns
the first child's complete resource, with no resource moved to a refused second child.
-/

open Zig Zig.Conc Zig.Full

namespace StrengthLog.SpawnFailure

example {own : ThreadId → Res} {rO : Res} {m : Mem} {P : Proto Target Unit}
    {G : ThreadId → Unit} {t depth : Nat} (ho : FOwned own rO m) :
    P.WP t ((spawnOutcomeC 1 Target.worker : CM Target Unit _).run ())
      (fun result _ m' _ => result = (.error "ThreadQuotaExceeded", ()) ∧ FOwned own rO m') G m depth :=
  failedSpawnOwnership ho

example {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t first c : ThreadId}
    {depth : Nat} (hc : c ≠ 0) (ho : FOwned own rO m) (ht : t < m.threads.size) (hne : first ≠ t)
    (hj : ((Thread.join first).run {m with current := t}).run = some (.ok ((), m'))) :
    (spawnOutcomeC c Target.worker : CM Target Unit _).run () depth {m with current := t} =
      CoN.leaf (some (.ok ((.error (spawnErrorAt (c - 1)), ()), {m with current := t}))) ∧
    FOwned (upd (upd own first rnil) t (rsum (own t) (own first))) rO m' :=
  refusedSecondThenJoin (depth := depth) hc ho ht hne hj

end StrengthLog.SpawnFailure
