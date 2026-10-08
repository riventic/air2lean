import ZigLean.Conc.Call

/-!
# Resource-sensitive thread assignment

`available` is an explicit environment permission: assignment succeeds. `fallible`
quantifies every listed API outcome. Failure does not fork, register a task, or
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

/-- Fallback executes the task in the caller's ConcM, with the caller's current thread,
clock, and captured pointer provenance. It creates no child, handle, or group entry. -/
def groupAsyncOutcomeC (choice : Nat) (group : Ptr) (io : Io) (target : Tgt)
    (fallback : ConcM Tgt Unit) : CM Tgt σ Unit :=
  if choice = 0 then groupAsyncC group io target else callC fallback

def groupAsyncWithPolicyC (policy : SpawnPolicy) (group : Ptr) (io : Io) (target : Tgt)
    (fallback : ConcM Tgt Unit) : CM Tgt σ Unit := do
  match policy with
  | .available => groupAsyncC group io target
  | .fallible =>
    let choice ← assignmentChoiceC 2
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
  cases policy with
  | available => exact monotone_const _
  | fallible =>
    unfold groupAsyncWithPolicyC
    apply monotone_bind _ _ _ (monotone_const _)
    apply monotone_of_monotone_apply
    intro choice
    by_cases hc : choice = 0
    · simpa only [groupAsyncOutcomeC, if_pos hc] using
        (monotone_const (groupAsyncC group io target : CM Tgt σ Unit) :
          monotone (fun _ : γ => (groupAsyncC group io target : CM Tgt σ Unit)))
    · simpa only [groupAsyncOutcomeC, if_neg hc] using (monotone_callC f hmono)

end Zig
