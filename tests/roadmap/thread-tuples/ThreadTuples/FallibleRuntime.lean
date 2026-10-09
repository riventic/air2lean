import ThreadTuplesFallible.Gen

/-! `groupMixed` translated with `--spawn-policy fallible`. Each `Group.async` may be assigned
or run eagerly, and `Group.concurrent` may fail with `error.ConcurrencyUnavailable`. When
`concurrent` fails after `mixedWorker` was assigned to a child, the function must still finish
that child before its frame (`out`, `other`, the group) is freed. Every sampled schedule must
end without a memory error, with no group entry left and every child joined. The suite must
cover that failing path. -/

open Zig

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  let mut assignedThenFailed := false
  let mut succeeded := false
  for seed in List.range 64 do
    for stride in [1, 3, 5, 7] do
      let oracle := fun turn => seed / (2 ^ (turn % 6)) + turn * stride
      match (Sched.run ThreadTuplesFallible.dispatch 500 oracle
          (ThreadTuplesFallible.groupMixed {} 10 2) {}).run with
      | some (.ok (result, m)) =>
        require m.groups.isEmpty s!"group entry outlived groupMixed: {seed}, {stride}"
        require (m.threads.all (fun r => r.spawner != 0 || r.joined))
          s!"unjoined group child outlived groupMixed: {seed}, {stride}"
        match result with
        | .ok n =>
          require (n.toNat == 680) s!"wrong groupMixed result {n.toNat}: {seed}, {stride}"
          succeeded := true
        | .error e =>
          require (e == "ConcurrencyUnavailable") s!"undeclared groupMixed error {e}"
          -- Thread 0 is main. Two children: both `async` calls, including `mixedWorker`,
          -- were assigned before `concurrent` failed (a failed `concurrent` adds none).
          if m.threads.size == 3 then assignedThenFailed := true
      | some (.error e) =>
        throw (IO.userError s!"groupMixed schedule {seed}, {stride} failed: {repr e}")
      | none => throw (IO.userError s!"groupMixed schedule {seed}, {stride} ran out of fuel")
  require (assignedThenFailed && succeeded)
    "fallible groupMixed oracles missed the assigned-then-failed or success path"
  IO.println "fallible groupMixed schedules awaited every child before freeing its frame"
