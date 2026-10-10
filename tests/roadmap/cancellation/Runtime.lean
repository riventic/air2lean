import Proofs.Cancel.Spurious
import Proofs.Cancel.Client

/-!
# C05 sampled schedules: spurious returns and cancelation

Every oracle prefix of `bits` binary choices (then option 0) is run for each client. These are
bounded samples; the all-schedules statements are `Proofs/Cancel/Group.lean` and the rebuilt
std sync proofs.

- `waitOnce` (no recheck) gives `0` under some sampled schedule and `1` under another.
- `waitLoop` (recheck) never gives `0` and never an error.
- `cancelClient` gives each of `(1, 3)`, `(2, 0)`, `(2, 1)`, `(2, 2)`, only `Outcome` results,
  never an error, and frees every block in every completed run.
- Two semantic mutants of the client (`cancel-is-await`, `canceled-status-dropped`) fail
  those checks.

Run with `lake env lean --run tests/roadmap/cancellation/Runtime.lean`.
-/

open Zig

def oracles (bits : Nat) : List (Nat → Nat) :=
  (List.range (2 ^ bits)).map fun mask => fun i => if i < bits then (mask >>> i) % 2 else 0

def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def spurious : IO Unit := do
  let mut onceValues : List (BitVec 32) := []
  for o in oracles 8 do
    match (Sched.run ⟨.any, .available⟩ Cancel.Spurious.dispatch 60 o Cancel.Spurious.waitOnce {}).run with
    | some (.ok (v, _)) => onceValues := v :: onceValues
    | some (.error e) => throw (IO.userError s!"waitOnce error {repr e}")
    | none => pure ()
    match (Sched.run ⟨.any, .available⟩ Cancel.Spurious.dispatch 80 o (Cancel.Spurious.waitLoop 6) {}).run with
    | some (.ok (v, _)) => require (v == 1) s!"waitLoop read {v}"
    | some (.error e) => throw (IO.userError s!"waitLoop error {repr e}")
    | none => pure ()
  require (onceValues.contains 0) "no sampled spurious schedule broke waitOnce"
  require (onceValues.contains 1) "no sampled schedule completed waitOnce"
  IO.println s!"spurious: waitOnce results {onceValues.eraseDups}, waitLoop always 1"

def cancel : IO Unit := do
  let mut seen : List (BitVec 32 × BitVec 32) := []
  for o in oracles 12 do
    match (Sched.run ⟨.any, .available⟩ Cancel.dispatch 80 o Cancel.cancelClient {}).run with
    | some (.ok (v, m)) =>
      require (decide (Cancel.Outcome v)) s!"cancelClient result {v} outside Outcome"
      require (m.blocks.all (!·.live)) "cancelClient left a live block"
      seen := v :: seen
    | some (.error e) => throw (IO.userError s!"cancelClient error {repr e}")
    | none => pure ()
  for r in [((1 : BitVec 32), (3 : BitVec 32)), (2, 0), (2, 1), (2, 2)] do
    require (seen.contains r) s!"cancelClient never gave {r}"
  IO.println s!"cancel: results {seen.eraseDups}"

/-! ## Semantic mutants of the client

Each mutant changes the client in one place; the checks of `cancel` above must reject it.

- `cancel-is-await`: `main` awaits the group instead of canceling it (the model before C05, where
  `Group.cancel` was `await`). No canceled result `(2, _)` is reachable any more.
- `canceled-status-dropped`: the task returns `error.Canceled` without its cleanup store of
  `status = 2`. The result `(0, d)` is outside `Outcome`.
-/

/-- `main`, awaiting the group instead of canceling it. -/
def awaitClient : ConcM Cancel.Tgt (BitVec 32 × BitVec 32) :=
  (do
    let status ← callMC (alloc .heap 4 4)
    callMC (store 4 status (0 : BitVec 32))
    let done ← callMC (alloc .heap 4 4)
    callMC (store 4 done (0 : BitVec 32))
    let g ← callMC (alloc .stack 16 8)
    groupAsyncC g ⟨⟩ (Cancel.Tgt.worker status done)
    spinLoopHintC
    discard (groupAwaitC g ⟨⟩)
    let s ← callMC (load (BitVec 32) 4 status)
    let d ← callMC (load (BitVec 32) 4 done)
    callMC (free status)
    callMC (free done)
    callMC (free g)
    pure (s, d) : CM Cancel.Tgt Unit (BitVec 32 × BitVec 32)).run' ()

/-- The worker's steps without the cleanup store on `error.Canceled`. -/
def droppedSteps (status done : Ptr) : Nat → Nat → CM Cancel.Tgt Unit Unit
  | _, 0 => callMC (store 4 status (1 : BitVec 32))
  | i, k + 1 => do
    match ← futexWaitCancelableC ⟨⟩ status (7 : BitVec 32) with
    | .error _ => pure ()
    | .ok () => do
      callMC (store 4 done (BitVec.ofNat 32 (i + 1)))
      droppedSteps status done (i + 1) k

def droppedDispatch : Cancel.Tgt → ConcM Cancel.Tgt Unit
  | .worker status done => (droppedSteps status done 0 3).run' ()

/-- The results of `client` under `d` over the sampled oracles. -/
def results (d : Cancel.Tgt → ConcM Cancel.Tgt Unit) (client : ConcM Cancel.Tgt (BitVec 32 × BitVec 32)) :
    List (BitVec 32 × BitVec 32) :=
  (oracles 12).filterMap fun o => match (Sched.run ⟨.any, .available⟩ d 80 o client {}).run with
    | some (.ok (v, _)) => some v
    | _ => none

def mutants : IO Unit := do
  let awaited := results Cancel.dispatch awaitClient
  require (!awaited.isEmpty && !awaited.any (·.1 == 2))
    "cancel-is-await: a canceled result is still reachable, so the check would not reject it"
  let dropped := results droppedDispatch Cancel.cancelClient
  require (dropped.any fun r => !decide (Cancel.Outcome r))
    "canceled-status-dropped: every sampled result is inside Outcome, so the check would not reject it"
  IO.println "cancel mutants: cancel-is-await and canceled-status-dropped rejected"

def main : IO Unit := do
  spurious
  cancel
  mutants
