
-- Appended to the fresh, policy-marked translation and elaborated/executed together.
private def requireOutcome (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def allowedSpawn (error : String) : Bool := Zig.spawnErrors.contains error
private def cleaned (m : Zig.Mem) : Bool :=
  m.groups.isEmpty && m.threads.all (fun rec => rec.spawner != 0 || rec.joined)

def main : IO Unit := do
  let mut failures : Array String := #[]
  let mut secondFailure := false
  let value := (17 : BitVec 32)
  -- This fixture's choice counts are 1, 2, 3 and 6, so the affine oracle
  -- repeats modulo 6. Revisit this bound if workers add choices or nested spawns.
  let fixtureChoicePeriod := 6
  for seed in List.range fixtureChoicePeriod do
    let oracle := fun turn => seed + turn * 11
    match (Zig.Sched.run SpawnFailure.dispatch 160 oracle (SpawnFailure.threadPair value) (SpawnFailure.mem0 .fresh)).run with
    | some (.ok (result, m)) =>
      requireOutcome (cleaned m) "SOURCE_REJECTED: pair cleanup leaked a child/group entry"
      match result with
      | .ok sum => requireOutcome (sum == 35) "SOURCE_REJECTED: pair result differs"
      | .error error =>
        requireOutcome (allowedSpawn error) "SOURCE_REJECTED: undeclared spawn error"
        if !failures.contains error then failures := failures.push error
        if m.threads.size == 2 then secondFailure := true
    | _ => throw (IO.userError "SOURCE_REJECTED: pair did not return safely")
  requireOutcome (failures.size == 5 && secondFailure)
    "SOURCE_REJECTED: missing failure alternatives or second-spawn cleanup"
  for (oracle, expected) in #[(fun _ : Nat => 0, value), (fun _ : Nat => 1, (0 : BitVec 32))] do
    match (Zig.Sched.run SpawnFailure.dispatch 100 oracle (SpawnFailure.threadCatch value) (SpawnFailure.mem0 .fresh)).run with
    | some (.ok (result, m)) =>
      requireOutcome (result == expected && cleaned m) "SOURCE_REJECTED: captured caller ownership lost"
    | _ => throw (IO.userError "SOURCE_REJECTED: caught spawn did not return safely")
  IO.println "SOURCE_THREAD_OUTCOMES_OK"
