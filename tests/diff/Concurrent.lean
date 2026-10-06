import Outcome
import Proofs.Threads.Gen
import Proofs.Atomics.Gen
import Proofs.Sync.Gen
import Proofs.Threadsync.Gen
import Proofs.Iogroup.Gen

namespace DiffConcurrent
open Lean (Json)
open DiffOutcome (Observation ReturnedError)

abbrev Runner := (Nat → Nat) → Observation × Array Nat

private def parse {α : Type} (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def args (j : Json) (n : Nat) : IO (Array Json) := do
  let a ← parse j.getArr?
  unless a.size == n do throw (IO.userError s!"expected {n} arguments")
  pure a

private def arg32 (a : Array Json) (i : Nat) : IO (BitVec 32) := do
  let v ← parse a[i]!.getInt?
  pure (BitVec.ofInt 32 v)

private def payload : Except Zig.ErrName (BitVec 32) → String
  | .error e => "{\"err\":\"" ++ e ++ "\"}"
  | .ok v => toString v.toNat

/-- Shared by observed-result matching, replay and enumeration. -/
def runWith {Tgt α : Type} [ReturnedError α] (fuel : Nat)
    (dispatch : Tgt → Zig.ConcM Tgt Unit) (m0 : Zig.Mem)
    (main : Zig.ConcM Tgt α) (render : α → String) : Runner := fun o =>
  let (r, opts) := Zig.Sched.runTrace dispatch fuel o main m0
  let out : Observation := match r with
    | none => DiffOutcome.noResult
    | some (.error e) => DiffOutcome.failure e
    | some (.ok (v, _)) => { line := "{\"ok\":" ++ render v ++ "}", kind := DiffOutcome.valueKind v }
  (out, opts)

/-- The same generated programs and dispatchers used by the differential runner. -/
def runner (ex name : String) (input : Json) (fuel : Nat) : IO Runner := do
  match ex with
  | "threads" =>
    let n := if name == "claimOnce" then 0 else if name == "parallelCounter" then 1 else 2
    let a ← args input n
    let main ← match name with
      | "parallelCounter" => pure (Threads.parallelCounter (← arg32 a 0))
      | "race" => pure (Threads.race (← arg32 a 0) (← arg32 a 1))
      | "disjoint" => pure (Threads.disjoint (← arg32 a 0) (← arg32 a 1))
      | "xchgRace" => pure (Threads.xchgRace (← arg32 a 0) (← arg32 a 1))
      | "claimOnce" => pure Threads.claimOnce
      | _ => throw (IO.userError s!"unknown concurrent function {ex}.{name}")
    pure (runWith fuel Threads.dispatch Threads.mem0 main payload)
  | "atomics" =>
    let _ ← args input 0
    let main ← match name with
      | "mpRelAcq" => pure Atomics.mpRelAcq
      | "mpRelaxed" => pure Atomics.mpRelaxed
      | "sbRelaxed" => pure Atomics.sbRelaxed
      | "twoPlusTwoW" => pure Atomics.twoPlusTwoW
      | "stackPush" => pure Atomics.stackPush
      | _ => throw (IO.userError s!"unknown concurrent function {ex}.{name}")
    pure (runWith fuel Atomics.dispatch Atomics.mem0 main payload)
  | "sync" =>
    let _ ← args input 0
    let main ← match name with
      | "mutexCounter" => pure (Sync.mutexCounter {})
      | "handoff" => pure (Sync.handoff {})
      | "semaphoreCounter" => pure (Sync.semaphoreCounter {})
      | "rwLockRead" => pure (Sync.rwLockRead {})
      | _ => throw (IO.userError s!"unknown concurrent function {ex}.{name}")
    pure (runWith fuel Sync.dispatch Sync.mem0 main payload)
  | "threadsync" =>
    let _ ← args input 0
    let main ← match name with
      | "mutexCounter" => pure Threadsync.mutexCounter
      | "handoff" => pure Threadsync.handoff
      | "waitGroup" => pure Threadsync.waitGroup
      | _ => throw (IO.userError s!"unknown concurrent function {ex}.{name}")
    pure (runWith fuel Threadsync.dispatch Threadsync.mem0 main payload)
  | "iogroup" =>
    let _ ← args input 0
    let main ← match name with
      | "groupCounter" => pure (Iogroup.groupCounter {})
      | "groupConcurrent" => pure (Iogroup.groupConcurrent {})
      | _ => throw (IO.userError s!"unknown concurrent function {ex}.{name}")
    pure (runWith fuel Iogroup.dispatch Iogroup.mem0 main payload)
  | _ => throw (IO.userError s!"unknown concurrent example {ex}")
end DiffConcurrent
