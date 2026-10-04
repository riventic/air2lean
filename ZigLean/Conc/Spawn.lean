import ZigLean.Conc.Call

/-!
# Resource-sensitive thread assignment

`available` is an explicit environment permission: assignment succeeds. `fallible`
quantifies every listed API outcome. Failure does not fork, register a task, or
transfer captures. The oracle choice is a scheduling point, so another thread may
run before the outcome is selected. These operations promise no progress.
-/

namespace Zig

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

variable {Tgt σ : Type}

/-- Outcome zero assigns a child; every other valid outcome returns a declared error.
The failure branch leaves memory and locals untouched, including captured pointers. -/
def spawnOutcomeC (choice : Nat) (target : Tgt) : CM Tgt σ (Except ErrName ThreadId) :=
  if choice = 0 then spawnC target else pure (.error (spawnErrorAt (choice - 1)))

/-- The available policy retains the historical proof contract; fallible exposes all
six outcomes, without granting a child protocol obligation on failure. -/
def spawnWithPolicyC (policy : SpawnPolicy) (target : Tgt) :
    CM Tgt σ (Except ErrName ThreadId) := do
  match policy with
  | .available => spawnC target
  | .fallible =>
    let choice ← pickC (fun _ => spawnErrors.size + 1)
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
    let choice ← pickC (fun _ => 2)
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
    let choice ← pickC (fun _ => 2)
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
    intro choice
    unfold groupAsyncOutcomeC
    split
    · exact monotone_const _
    · exact monotone_callC f hmono

end Zig
