
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
  -- In an `available` environment only the translation's `fallible` policy can fail a spawn, so
  -- the failures collected there are the translation's own alternatives. In a `fallible`
  -- environment each spawn makes a second failure choice (the environment's), which no affine
  -- oracle sets to 0 together with the policy's; the prefix oracles (option 0 for the first `k`
  -- choices, then option 1) reach a first spawn that succeeds and a second that fails.
  let fixtureChoicePeriod := 6
  let affine := (List.range fixtureChoicePeriod).map fun seed => fun turn => seed + turn * 11
  let prefixes := (List.range 24).map fun k => fun turn => if turn < k then 0 else 1
  let runs : List (Zig.Env × (Nat → Nat)) :=
    affine.map (fun o => (⟨.threaded 1, .available⟩, o)) ++
      (affine ++ prefixes).map (fun o => (⟨.threaded 1, .fallible⟩, o))
  for (env, oracle) in runs do
    match (Zig.Sched.run env SpawnFailure.dispatch 160 oracle (SpawnFailure.threadPair value) (SpawnFailure.mem0 .fresh)).run with
    | some (.ok (result, m)) =>
      requireOutcome (cleaned m) "SOURCE_REJECTED: pair cleanup leaked a child/group entry"
      match result with
      | .ok sum => requireOutcome (sum == 35) "SOURCE_REJECTED: pair result differs"
      | .error error =>
        requireOutcome (allowedSpawn error) "SOURCE_REJECTED: undeclared spawn error"
        if env.spawn == .available && !failures.contains error then failures := failures.push error
        if m.threads.size == 2 then secondFailure := true
    | _ => throw (IO.userError "SOURCE_REJECTED: pair did not return safely")
  requireOutcome (failures.size == 5 && secondFailure)
    "SOURCE_REJECTED: missing failure alternatives or second-spawn cleanup"
  for (oracle, expected) in #[(fun _ : Nat => 0, value), (fun _ : Nat => 1, (0 : BitVec 32))] do
    match (Zig.Sched.run ⟨.threaded 1, .fallible⟩ SpawnFailure.dispatch 100 oracle (SpawnFailure.threadCatch value) (SpawnFailure.mem0 .fresh)).run with
    | some (.ok (result, m)) =>
      requireOutcome (result == expected && cleaned m) "SOURCE_REJECTED: captured caller ownership lost"
    | _ => throw (IO.userError "SOURCE_REJECTED: caught spawn did not return safely")
  IO.println "SOURCE_THREAD_OUTCOMES_OK"
