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
    match (Sched.run Cancel.Spurious.dispatch 60 o Cancel.Spurious.waitOnce {}).run with
    | some (.ok (v, _)) => onceValues := v :: onceValues
    | some (.error e) => throw (IO.userError s!"waitOnce error {repr e}")
    | none => pure ()
    match (Sched.run Cancel.Spurious.dispatch 80 o (Cancel.Spurious.waitLoop 6) {}).run with
    | some (.ok (v, _)) => require (v == 1) s!"waitLoop read {v}"
    | some (.error e) => throw (IO.userError s!"waitLoop error {repr e}")
    | none => pure ()
  require (onceValues.contains 0) "no sampled spurious schedule broke waitOnce"
  require (onceValues.contains 1) "no sampled schedule completed waitOnce"
  IO.println s!"spurious: waitOnce results {onceValues.eraseDups}, waitLoop always 1"

def cancel : IO Unit := do
  let mut seen : List (BitVec 32 × BitVec 32) := []
  for o in oracles 12 do
    match (Sched.run Cancel.dispatch 80 o Cancel.cancelClient {}).run with
    | some (.ok (v, m)) =>
      require (decide (Cancel.Outcome v)) s!"cancelClient result {v} outside Outcome"
      require (m.blocks.all (!·.live)) "cancelClient left a live block"
      seen := v :: seen
    | some (.error e) => throw (IO.userError s!"cancelClient error {repr e}")
    | none => pure ()
  for r in [((1 : BitVec 32), (3 : BitVec 32)), (2, 0), (2, 1), (2, 2)] do
    require (seen.contains r) s!"cancelClient never gave {r}"
  IO.println s!"cancel: results {seen.eraseDups}"

def main : IO Unit := do
  spurious
  cancel
