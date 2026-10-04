  for (oracle, childCount) in #[(fun _ : Nat => 0, 2), (fun _ : Nat => 1, 1)] do
    match (Zig.Sched.run SpawnFailure.dispatch 100 oracle (SpawnFailure.groupAsync {} value) SpawnFailure.mem0).run with
    | some (.ok (.ok result, m)) =>
      requireOutcome (result == value && m.threads.size == childCount && cleaned m)
        "SOURCE_REJECTED: async child/fallback result or publication differs"
    | _ => throw (IO.userError "SOURCE_REJECTED: group async did not return safely")
  match (Zig.Sched.run SpawnFailure.dispatch 100 (fun _ => 1)
      (SpawnFailure.groupConcurrent {} value) SpawnFailure.mem0).run with
  | some (.ok (.error error, m)) =>
    requireOutcome (error == "ConcurrencyUnavailable" && m.threads.size == 1 && cleaned m)
      "SOURCE_REJECTED: rejected concurrent task was published"
  | _ => throw (IO.userError "SOURCE_REJECTED: concurrent failure was lost")
  IO.println "SOURCE_GROUP_OUTCOMES_OK"
