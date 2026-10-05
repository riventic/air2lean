import Lean
import ZigLean.Sep.Alloc

open Zig

private def checkCase (name : String) (cap : Nat) (failures : List Nat) (failAt : Option Nat)
    (sizes : List Nat) (expected : List Bool) : IO Unit := do
  let m : Mem := { failAt, allocPolicy := { maxBytes := cap, failures } }
  match ((releaseAttempts sizes 1).run m).run with
  | some (.ok (oks, final)) =>
    unless oks = expected ∧ final.allocs = sizes.length ∧
        final.blocks.all (fun b => !b.live) do
      throw (IO.userError s!"{name}: outcome, attempt count or cleanup mismatch")
    IO.println (Lean.Json.mkObj [
      ("case", Lean.toJson name),
      ("outcomes", Lean.toJson (oks.map fun b => if b then (1 : Nat) else 0)),
      ("attempts", Lean.toJson final.allocs),
      ("live", Lean.toJson (0 : Nat))]).compress
  | _ => throw (IO.userError s!"{name}: modeled error or missing result")

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
