import SpawnFailure.Gen

/-!
Executions of the checked fallible translation under per-caller thread budgets
(`Mem.spawnLimit`). Several assignments fail in one run; at an exhausted budget the result does
not depend on the failure oracle. These are finite executions, not proofs; the proofs over every
schedule, outcome and budget are `SpawnFailure.Group` and `SpawnFailure.Pair`.
-/

open Zig

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def cleaned (m : Mem) : Bool :=
  m.groups.isEmpty && m.threads.all (fun r => r.spawner != 0 || r.joined)

private def withLimit (limit : Option Nat) : Mem := { SpawnFailure.mem0 with spawnLimit := limit }

private def children (m : Mem) : Nat := m.threads.size - 1

/-- Three spawn sites in one run: two caught spawns and the pair (two more sites). -/
private def several : ConcM SpawnFailure.Tgt (BitVec 32 × BitVec 32 × Except ErrName (BitVec 32)) := do
  let a ← SpawnFailure.threadCatch 5
  let b ← SpawnFailure.threadCatch 6
  let c ← SpawnFailure.threadPair 7
  pure (a, b, c)

/-- Two group clients in one run. -/
private def groups : ConcM SpawnFailure.Tgt (Except ErrName (BitVec 32) × Except ErrName (BitVec 32)) := do
  let a ← SpawnFailure.groupAsync {} 11
  let b ← SpawnFailure.groupConcurrent {} 12
  pure (a, b)

-- The oracle counts of these clients are at most 6, so 12 affine seeds cover every choice
-- residue at each turn; revisit if the clients gain choices.
private def seeds : List Nat := List.range 12

def main : IO Unit := do
  for seed in seeds do
    let oracle := fun turn => seed + turn * 7
    -- Budget 0: every assignment fails, in every schedule and for every oracle.
    match (Sched.run SpawnFailure.dispatch 400 oracle several (withLimit (some 0))).run with
    | some (.ok ((a, b, c), m)) =>
      require (a == 0 && b == 0 && children m == 0 && cleaned m)
        "budget 0: a caught spawn assigned a child or lost its capture"
      match c with
      | .error e => require (spawnErrors.contains e) "budget 0: undeclared spawn error"
      | .ok _ => throw (IO.userError "budget 0: the pair assigned a child")
    | _ => throw (IO.userError "budget 0: run did not return safely")
    -- Budget 1: the pair's second assignment always fails while child 1 is live; it is joined.
    match (Sched.run SpawnFailure.dispatch 400 oracle (SpawnFailure.threadPair 7) (withLimit (some 1))).run with
    | some (.ok (.error e, m)) =>
      require (spawnErrors.contains e && children m ≤ 1 && cleaned m)
        "budget 1: the second failure leaked the first child"
    | _ => throw (IO.userError "budget 1: the pair returned without a failure")
    -- Budget 0: async runs in the caller, concurrent reports the declared error.
    match (Sched.run SpawnFailure.dispatch 400 oracle groups (withLimit (some 0))).run with
    | some (.ok ((a, b), m)) =>
      require (a == .ok 11 && b == .error "ConcurrencyUnavailable" && children m == 0 && cleaned m)
        "budget 0: group fallback or concurrency failure differs"
    | _ => throw (IO.userError "budget 0: group run did not return safely")
  -- Budget 2 with an always-assigning oracle: no failure, and the contract value.
  match (Sched.run SpawnFailure.dispatch 400 (fun _ => 0) several (withLimit (some 2))).run with
  | some (.ok ((a, b, c), m)) =>
    require (a == 5 && b == 6 && c == .ok 15 && children m == 4 && cleaned m)
      "budget 2: assignments below the budget failed"
  | _ => throw (IO.userError "budget 2: run did not return safely")
  -- Fallback and assignment give the same declared result.
  for (limit, kids) in [(some 0, 0), (none, 1)] do
    match (Sched.run SpawnFailure.dispatch 200 (fun _ => 0) (SpawnFailure.groupAsync {} 9)
        (withLimit limit)).run with
    | some (.ok (r, m)) =>
      require (r == .ok 9 && children m == kids && cleaned m) "group async result differs"
    | _ => throw (IO.userError "group async did not return safely")
  IO.println "spawn budget executions passed"
