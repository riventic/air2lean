import ZigLean
import ZigLean.Conc.SpawnLemmas
import ZigLean.Conc.Csl

open Zig Zig.Conc

inductive Target where
  | worker

private def dispatch : Target → ConcM Target Unit := fun _ => pure ()

-- These kernel equalities do not run a host compiler or depend on scheduler fuel.
-- They expose the exact failure leaf, including every field of arbitrary memory.
theorem failedSpawnLeaf (c : Nat) (hc : c ≠ 0) (s : Unit) (m : Mem) (depth : Nat) :
    (spawnOutcomeC c Target.worker : CM Target Unit _).run s depth m =
      CoN.leaf (some (.ok ((.error (spawnErrorAt (c - 1)), s), m))) := by
  simp only [spawnOutcomeC, if_neg hc]
  rfl

theorem failedConcurrentLeaf (s : Unit) (m : Mem) (depth : Nat) :
    (groupConcurrentOutcomeC 1 (⟨none, 0⟩ : Ptr) {} Target.worker : CM Target Unit _).run s depth m =
      CoN.leaf (some (.ok ((.error "ConcurrencyUnavailable", s), m))) := by rfl

theorem eagerCallerBody (fallback : ConcM Target Unit) (g : Ptr) (s : Unit) :
    (groupAsyncOutcomeC 1 g {} Target.worker fallback : CM Target Unit Unit).run s =
      (callC fallback : CM Target Unit Unit).run s := by rfl

-- Arbitrary ownership and cleanup obligations stay with the caller on failure.
theorem failedSpawnOwnership {own : ThreadId → Heap} {m : Mem} {P : Proto Target Unit}
    {G : ThreadId → Unit} {t depth : Nat} (ho : Owned own m) :
    P.WP t ((spawnOutcomeC 1 Target.worker : CM Target Unit _).run ())
      (fun result _ m' _ => result = (.error "ThreadQuotaExceeded", ()) ∧ Owned own m') G m depth := by
  exact Proto.WP.spawnFailureFrame (by decide) ho


-- The refused second capture stays in the parent's private heap. Joining the
-- earlier child then merges only that child's disjoint part into the caller.
-- Both claims hold for arbitrary memory and every failed assignment choice.
theorem refusedSecondThenJoin {own : ThreadId → Heap} {m m' : Mem} {t first c : ThreadId}
    {depth : Nat} (hc : c ≠ 0) (ho : Owned own m) (ht : t < m.threads.size)
    (hne : first ≠ t)
    (hj : ((Thread.join first).run {m with current := t}).run = some (.ok ((), m'))) :
    (spawnOutcomeC c Target.worker : CM Target Unit _).run () depth {m with current := t} =
      CoN.leaf (some (.ok ((.error (spawnErrorAt (c - 1)), ()), {m with current := t}))) ∧
    Owned (upd (upd own t (own t ∪ own first)) first Heap.empty) m' := by
  exact ⟨failedSpawnLeaf c hc () _ depth, Owned.join ho ht hne hj⟩

-- At an exhausted budget the oracle range holds only the five errors, and no choice
-- decodes to assignment.
theorem exhaustedBudgetExcludesAssignment (m : Mem) (h : m.spawnLimit = some 0) :
    assignmentCount (spawnErrors.size + 1) m = spawnErrors.size ∧
      ∀ c, assignmentOutcome m.spawnAdmits c ≠ 0 := by
  have ha : m.spawnAdmits = false := by simp [Mem.spawnAdmits, h]
  refine ⟨by simp [assignmentCount, ha], fun c => ?_⟩
  simp [assignmentOutcome, ha]

theorem noBudgetKeepsEveryOutcome (m : Mem) (h : m.spawnLimit = none) (total : Nat) :
    assignmentCount total m = total ∧ ∀ c, assignmentOutcome m.spawnAdmits c = c := by
  have ha : m.spawnAdmits = true := by simp [Mem.spawnAdmits, h]
  exact ⟨by simp [assignmentCount, ha], fun c => by simp [assignmentOutcome, ha]⟩

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def failedCalls : ConcM Target (Except ErrName ThreadId × Except ErrName Unit) := do
  let first ← (spawnWithPolicyC .fallible .worker : CM Target Unit _).run' ()
  match first with
  | .ok child => discard ((joinC child : CM Target Unit Unit).run' ())
  | .error _ => pure ()
  let second ← (groupConcurrentWithPolicyC .fallible (⟨none, 0⟩ : Ptr) {} .worker : CM Target Unit _).run' ()
  match second with
  | .ok _ => discard ((groupAwaitC (⟨none, 0⟩ : Ptr) {} : CM Target Unit _).run' ())
  | .error _ => pure ()
  pure (first, second)

-- The eager task records its actual caller id in memory. A fork would change it.
private def eagerCaller : ConcM Target ThreadId := do
  let body : ConcM Target Unit := ConcM.liftMem (modify fun m => {m with nextMsg := m.current + 41})
  discard ((groupAsyncWithPolicyC .fallible (⟨none, 0⟩ : Ptr) {} .worker body : CM Target Unit Unit).run' ())
  let m ← ConcM.liftMem get
  pure m.nextMsg

-- Five assignments before any join: a budget of two live children refuses at least three.
private def fiveSpawns : ConcM Target (Array (Except ErrName ThreadId)) := do
  let mut results := #[]
  for _ in [0:5] do
    let r ← (spawnWithPolicyC .fallible .worker : CM Target Unit _).run' ()
    results := results.push r
  for r in results do
    match r with
    | .ok child => discard ((joinC child : CM Target Unit Unit).run' ())
    | .error _ => pure ()
  pure results

private def failures (rs : Array (Except ErrName ThreadId)) : Nat :=
  (rs.filter fun r => match r with | .error _ => true | .ok _ => false).size

private def budgetRuns : IO Unit := do
  for seed in List.range 12 do
    let oracle := fun turn => seed + turn * 7
    match (Sched.run ⟨.threaded 1, .fallible⟩ dispatch 200 oracle fiveSpawns { spawnLimit := some 2 }).run with
    | some (.ok (rs, m)) =>
      require (failures rs ≥ 3 && m.threads.size ≤ 3) "budget exceeded"
      require (rs.all fun r => match r with | .error e => spawnErrors.contains e | .ok _ => true)
        "undeclared spawn error under budget"
      require (m.threads.all (fun r => r.spawner != 0 || r.joined)) "budgeted child leaked"
    | _ => throw (IO.userError "budgeted fixture did not return safely")
  match (Sched.run ⟨.threaded 1, .fallible⟩ dispatch 200 (fun _ => 0) fiveSpawns { spawnLimit := some 2 }).run with
  | some (.ok (rs, _)) =>
    require (failures rs == 3 && (rs.extract 0 2).all (fun r => match r with | .ok _ => true | _ => false))
      "assignments below the budget were refused"
  | _ => throw (IO.userError "budgeted fixture did not return safely")
  match (Sched.run ⟨.threaded 1, .fallible⟩ dispatch 20 (fun _ => 0) eagerCaller { spawnLimit := some 0 }).run with
  | some (.ok (value, m)) =>
    require (value == 41 && m.threads.size == 1 && m.groups.isEmpty)
      "exhausted budget did not force the caller fallback"
  | _ => throw (IO.userError "budgeted eager fixture failed")

def main : IO Unit := do
  budgetRuns
  let mut errors : Array String := #[]
  let mut concurrentFailure := false
  -- This fixture's choice counts are 1, 2, 3 and 6, so the affine oracle
  -- repeats modulo 6. Revisit this bound if workers add choices or nested spawns.
  let fixtureChoicePeriod := 6
  for seed in List.range fixtureChoicePeriod do
    let oracle := fun turn => seed + turn * 11
    match (Sched.run ⟨.threaded 1, .fallible⟩ dispatch 80 oracle failedCalls {}).run with
    | some (.ok ((first, second), m)) =>
      require (m.groups.isEmpty) "group entry leaked after await/failure"
      require (m.threads.all (fun r => r.spawner != 0 || r.joined)) "unjoined child leaked"
      match first with
      | .error e =>
        require (spawnErrors.contains e) "undeclared spawn error"
        if !errors.contains e then errors := errors.push e
      | .ok _ => pure ()
      match second with
      | .error e =>
        require (e == "ConcurrencyUnavailable") "wrong group concurrent error"
        concurrentFailure := true
      | .ok _ => pure ()
    | _ => throw (IO.userError "finite resource fixture did not return safely")
  require (errors.size == 5 && concurrentFailure) "oracle suite did not cover failure alternatives"
  match (Sched.run ⟨.threaded 1, .fallible⟩ dispatch 20 (fun _ => 1) eagerCaller {}).run with
  | some (.ok (value, m)) =>
    require (value == 41 && m.threads.size == 1 && m.groups.isEmpty)
      "eager fallback created a child/group entry or used another current thread"
  | _ => throw (IO.userError "eager caller fixture failed")
  IO.println "spawn failure kernel frames and runtime outcomes passed"
