import ZigLean.Conc.Call

/-!
# Resource-sensitive thread assignment

`available` is an explicit environment permission: assignment succeeds. `fallible`
quantifies every listed API outcome. `Io.Group.async` is an oracle choice under both policies:
a thread, the caller (eager) or deferred until `await` (`groupAsyncWithPolicyC`), because std
promises none of them. Failure does not fork, register a task, or
transfer captures. The oracle choice is a scheduling point, so another thread may
run before the outcome is selected. These operations promise no progress.

**Resource budget.** `Mem.spawnLimit` (default `none`) bounds the assigned children of the
calling thread that no join has reclaimed (`Mem.liveChildren`). While the caller is at its
budget, the fallible oracle range excludes assignment: `Thread.spawn` returns one of the
declared errors, `Group.async` runs the task in the caller, and `Group.concurrent` returns
`ConcurrencyUnavailable`. Below the budget every outcome remains possible, so several
assignments in one run can fail by budget, by the oracle, or both. Only the caller creates or
joins its own children, so no other thread can change its count between the choice and the
assignment. The budget is per calling thread; it does not model a process-wide quota, stack
memory accounting, or the frequency of native failures. The `available` policy ignores it.
-/

namespace Zig

/-- The assigned children of thread `t` that no join has reclaimed. -/
def Mem.liveChildren (m : Mem) (t : ThreadId) : Nat :=
  (m.threads.filter fun r => r.spawner == t && !r.joined).size

/-- The current thread may receive another child under `Mem.spawnLimit`. -/
def Mem.spawnAdmits (m : Mem) : Bool :=
  match m.spawnLimit with
  | none => true
  | some limit => decide (m.liveChildren m.current < limit)

inductive SpawnPolicy where
  | available
  | fallible
  deriving DecidableEq, Repr, Inhabited

/-- The exact declared SpawnError set in std.Thread 0.14.1, 0.15.2, and 0.16.0.
The model does not predict which platform resource fails or its frequency. -/
def spawnErrors : Array ErrName :=
  #["ThreadQuotaExceeded", "SystemResources", "OutOfMemory",
    "LockedMemoryLimitExceeded", "Unexpected"]

/-- A total lookup; the fallback only covers malformed direct callers. -/
def spawnErrorAt (choice : Nat) : ErrName := spawnErrors[choice]?.getD "Unexpected"

/-- The oracle range of a resource choice with `total` outcomes, where outcome 0 assigns a
child: without budget for the caller, outcome 0 is not in the range. -/
def assignmentCount (total : Nat) (m : Mem) : Nat :=
  if m.spawnAdmits then total else total - 1

/-- The outcome of oracle choice `c`: without budget, choice `c` means outcome `c + 1`. -/
def assignmentOutcome (admits : Bool) (c : Nat) : Nat :=
  if admits then c else c + 1

variable {Tgt σ : Type}

/-- A resource choice among `total` outcomes (outcome 0 assigns a child). The budget is read in
the memory at which the caller resumes, with no scheduling point in between. -/
def assignmentChoiceC (total : Nat) : CM Tgt σ Nat := do
  let c ← pickC (assignmentCount total)
  let admits ← callMC (do pure (← get).spawnAdmits)
  pure (assignmentOutcome admits c)

/-- Outcome zero assigns a child; every other valid outcome returns a declared error.
The failure branch leaves memory and locals untouched, including captured pointers. -/
def spawnOutcomeC (choice : Nat) (target : Tgt) : CM Tgt σ (Except ErrName ThreadId) :=
  if choice = 0 then spawnC target else pure (.error (spawnErrorAt (choice - 1)))

/-- The available policy retains the historical proof contract; fallible exposes all
six outcomes (only the five errors at an exhausted budget), without granting a child protocol
obligation on failure. -/
def spawnWithPolicyC (policy : SpawnPolicy) (target : Tgt) :
    CM Tgt σ (Except ErrName ThreadId) := do
  match policy with
  | .available => spawnC target
  | .fallible =>
    let choice ← assignmentChoiceC (spawnErrors.size + 1)
    spawnOutcomeC choice target

/-- The executions of an `Io.Group.async` task: a new thread (0), the caller now (1, eager) or
deferred until the group's `await` or `cancel` (2). std 0.16.0 promises none of them
(`Io.Group.async`: the task is "not guaranteed to run until `await` or `cancel`"); `Io.Threaded`
runs it in the caller when `async_limit` (default CPU count − 1) tasks are busy, always under
`single_threaded`, and on a resource failure. -/
def groupAsyncOutcomes : Nat := 3

/-- Outcome 0 assigns a thread; outcome 1 executes the task in the caller's ConcM, with the
caller's current thread, clock, and captured pointer provenance (no child, handle, or group
entry); outcome 2 defers it (`groupDeferC`). -/
def groupAsyncOutcomeC (choice : Nat) (group : Ptr) (io : Io) (target : Tgt)
    (fallback : ConcM Tgt Unit) : CM Tgt σ Unit :=
  if choice = 0 then groupAsyncC group io target
  else if choice = 1 then callC fallback
  else groupDeferC group io target

/-- The oracle range of `Group.async` under the `fallible` policy: without budget for the
caller, only the caller execution (outcome 1) is left; the other two make a model thread. -/
def asyncCount (m : Mem) : Nat := if m.spawnAdmits then groupAsyncOutcomes else 1

/-- The outcome of oracle choice `c`: without budget, always the caller execution. -/
def asyncOutcome (admits : Bool) (c : Nat) : Nat := if admits then c else 1

/-- The budgeted choice of `Group.async` (as `assignmentChoiceC`). -/
def asyncChoiceC : CM Tgt σ Nat := do
  let c ← pickC asyncCount
  let admits ← callMC (do pure (← get).spawnAdmits)
  pure (asyncOutcome admits c)

/-- `Io.Group.async` under every policy: an oracle choice among the three executions
(`groupAsyncOutcomes`). The `fallible` policy only adds the budget: at an exhausted budget the
task runs in the caller (`asyncChoiceC`).

The oracle stands for the decision that `Io.Threaded.groupAsync` makes from its own state
(`busy_count`, `async_limit`, allocation and `Thread.spawn` results). A translation of
`Io.Threaded` from its AIR, with only the OS primitives trusted, can replace it: its
`groupAsync` then makes that decision itself, and each outcome here is one of its paths. -/
def groupAsyncWithPolicyC (policy : SpawnPolicy) (group : Ptr) (io : Io) (target : Tgt)
    (fallback : ConcM Tgt Unit) : CM Tgt σ Unit :=
  match policy with
  | .available => do
    let choice ← pickC fun _ => groupAsyncOutcomes
    groupAsyncOutcomeC choice group io target fallback
  | .fallible => do
    let choice ← asyncChoiceC
    groupAsyncOutcomeC choice group io target fallback

/-- Unlike async, concurrent never runs the task synchronously on failure. -/
def groupConcurrentOutcomeC (choice : Nat) (group : Ptr) (io : Io) (target : Tgt) :
    CM Tgt σ (Except ErrName Unit) :=
  if choice = 0 then groupConcurrentC group io target else pure (.error "ConcurrencyUnavailable")

def groupConcurrentWithPolicyC (policy : SpawnPolicy) (group : Ptr) (io : Io) (target : Tgt) :
    CM Tgt σ (Except ErrName Unit) := do
  match policy with
  | .available => groupConcurrentC group io target
  | .fallible =>
    let choice ← assignmentChoiceC 2
    groupConcurrentOutcomeC choice group io target

open Lean.Order in
@[partial_fixpoint_monotone]
theorem monotone_groupAsyncWithPolicyC {γ : Type} [PartialOrder γ]
    (policy : SpawnPolicy) (group : Ptr) (io : Io) (target : Tgt)
    (f : γ → ConcM Tgt Unit) (hmono : monotone f) :
    monotone (fun x => (groupAsyncWithPolicyC policy group io target (f x) : CM Tgt σ Unit)) := by
  have hout : ∀ choice, monotone (fun x =>
      (groupAsyncOutcomeC choice group io target (f x) : CM Tgt σ Unit)) := by
    intro choice
    by_cases h0 : choice = 0
    · simpa only [groupAsyncOutcomeC, if_pos h0] using
        (monotone_const (groupAsyncC group io target : CM Tgt σ Unit) :
          monotone (fun _ : γ => (groupAsyncC group io target : CM Tgt σ Unit)))
    by_cases h1 : choice = 1
    · simpa only [groupAsyncOutcomeC, if_neg h0, if_pos h1] using (monotone_callC f hmono)
    · simpa only [groupAsyncOutcomeC, if_neg h0, if_neg h1] using
        (monotone_const (groupDeferC group io target : CM Tgt σ Unit) :
          monotone (fun _ : γ => (groupDeferC group io target : CM Tgt σ Unit)))
  cases policy <;>
  · apply monotone_bind _ _ _ (monotone_const _)
    exact monotone_of_monotone_apply _ hout

end Zig
