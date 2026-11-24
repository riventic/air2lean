import Lean
import ZigLean.Mem

/-! The native comparison of M03: the `std` allocator model's `rawAlloc` under each policy
(failure index and list, request cap, failure oracle over (attempt, bytes), live-heap budget)
against `TestAllocator` (`fixture.zig`). A legacy std allocator model check
(`docs/alloc-spec.md`, §Retired claims). -/

open Zig

/-- One request per size: each success is freed at once; the result is the success flags. -/
private def releaseAttempts (sizes : List Nat) : MemM (List Bool × Option Nat) := do
  let oks ← sizes.mapM fun n => do
    let p ← rawAlloc n 1
    if let some p := p then rawFree p n
    pure p.isSome
  pure (oks, none)

/-- One request per size, every success held until the last request, so that the live heap
counts against a budget; also the live heap bytes before the frees. -/
private def heldAttempts (sizes : List Nat) : MemM (List Bool × Option Nat) := do
  let ps ← sizes.mapM fun n => do pure (← rawAlloc n 1, n)
  let held := (← get).liveHeapBytes
  for (p, n) in ps do
    if let some p := p then rawFree p n
  pure (ps.map (·.1.isSome), some held)

/-- The run from memory `m` (its policy), compared with the expected outcomes. -/
private def checkPolicy (name : String) (m : Mem) (hold : Bool) (sizes : List Nat)
    (expected : List Bool) : IO Unit := do
  match ((if hold then heldAttempts sizes else releaseAttempts sizes).run m).run with
  | some (.ok ((oks, held), final)) =>
    unless oks = expected ∧ final.allocs = sizes.length ∧
        final.blocks.all (fun b => !b.live) do
      throw (IO.userError s!"{name}: outcome, attempt count or cleanup mismatch")
    IO.println (Lean.Json.mkObj ([
      ("case", Lean.toJson name),
      ("outcomes", Lean.toJson (oks.map fun b => if b then (1 : Nat) else 0)),
      ("attempts", Lean.toJson final.allocs)] ++
      (held.map fun h => ("held", Lean.toJson h)).toList ++
      [("live", Lean.toJson (0 : Nat))])).compress
  | _ => throw (IO.userError s!"{name}: modeled error or missing result")

private def checkCase (name : String) (cap : Nat) (failures : List Nat) (failAt : Option Nat)
    (sizes : List Nat) (expected : List Bool) : IO Unit :=
  checkPolicy name { failAt, allocPolicy := { maxBytes := cap, failures } } false sizes expected

private def checkZero : IO Unit := do
  let m : Mem := { allocPolicy := { maxBytes := 0, failures := [0] } }
  match ((Allocator.alloc {} 1 1 0).run m).run with
  | some (.ok (.ok s, final)) =>
    unless s.len = 0 ∧ final.allocs = 0 ∧ final.blocks.isEmpty do
      throw (IO.userError "zero-size allocation consumed a policy decision")
  | _ => throw (IO.userError "zero-size allocation failed")
  IO.println "{\"case\":\"zero\",\"outcomes\":[1],\"attempts\":0,\"live\":0}"

def main : IO Unit := do
  checkCase "legacy-success" maxAllocBytes [] none [8, 8] [true, true]
  checkCase "legacy-failure" maxAllocBytes [] (some 0) [8, 8] [false, true]
  checkCase "several-failures" maxAllocBytes [0, 2] none [8, 8, 8, 8] [false, true, false, true]
  checkCase "combined" maxAllocBytes [2] (some 0) [8, 8, 8] [false, true, false]
  checkCase "duplicate-indices" maxAllocBytes [0, 0, 2] none [8, 8, 8] [false, true, false]
  checkCase "all-fail" maxAllocBytes [0, 1, 2] none [8, 8, 8] [false, false, false]
  checkCase "cap-boundary" 32 [] none [32, 33, 16] [true, false, true]
  checkCase "raised-cap" (2 * maxAllocBytes) [] none [maxAllocBytes + 1] [true]
  checkCase "default-cap" maxAllocBytes [] none [maxAllocBytes + 1] [false]
  checkZero
  -- The failure oracle over (attempt, bytes) and the live-heap budget. Each oracle is a Lean
  -- function here and a list of `TestAllocator.OracleRule` in `fixture.zig`.
  let policy (P : AllocPolicy) : Mem := { allocPolicy := P }
  checkPolicy "oracle-even-attempts" (policy { fails := fun i _ => i % 2 == 0 }) false
    [8, 8, 8, 8, 8, 8] [false, true, false, true, false, true]
  checkPolicy "oracle-by-size" (policy { fails := fun _ n => 16 < n }) false
    [8, 32, 16, 17] [true, false, true, false]
  checkPolicy "oracle-attempt-and-size" (policy { fails := fun i n => 2 ≤ i && n ≤ 8 }) false
    [8, 8, 8, 16, 4] [true, true, false, true, false]
  checkPolicy "oracle-two-rules" (policy { fails := fun i n => i == 1 || 64 ≤ n }) false
    [8, 8, 64, 8] [true, false, false, true]
  checkPolicy "oracle-all" (policy { fails := fun _ _ => true }) false [8, 8, 8] [false, false, false]
  checkPolicy "oracle-with-list-and-cap"
    (policy { maxBytes := 32, failures := [1], fails := fun i _ => i % 3 == 2 }) false
    [8, 8, 8, 33, 32, 8] [true, false, false, false, true, false]
  checkPolicy "budget-held" (policy { budget := some 20 }) true
    [8, 8, 8, 4, 1] [true, true, false, true, false]
  checkPolicy "budget-released" (policy { budget := some 8 }) false [8, 8, 9, 8] [true, true, false, true]
  checkPolicy "budget-zero" (policy { budget := some 0 }) false [1, 8] [false, false]
  checkPolicy "budget-and-oracle" (policy { budget := some 16, fails := fun i _ => i == 0 }) true
    [8, 8, 8, 8] [false, true, true, false]
