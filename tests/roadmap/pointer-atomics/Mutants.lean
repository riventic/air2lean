import Proofs.Atomics.PtrPublish

/-!
# C09 pointer publication: semantic mutants of the client

`publishRead_safe` (every oracle and fuel: no error) and `publishRead_spec` (the result is 0 or
42) are kernel theorems about the unmutated client (`Proofs/Atomics/PtrPublish.lean`). These
bounded runtime witnesses show that they depend on the release/acquire publication of the
pointer and on join-before-free, so the proofs are not vacuous:

- `relaxed-pointer-publish`: the producer stores the node's pointer with `.relaxed` instead of
  `.release`. The consumer's acquire load can read the pointer without synchronizing with the
  producer's write of 42, so its read of the node races (`.illegal`) on a sampled schedule.
- `free-before-join`: `main` destroys the node it read before it joins the producer. Its
  join-before-free destroy after the join then frees the same node again (`.illegal`).

Run: `lake env lean --run tests/roadmap/pointer-atomics/Mutants.lean` (after
`lake build Proofs.Atomics.PtrPublish`).
-/

open Zig Atomics.PtrPublish

/-- The producer, publishing the node with a relaxed store. -/
def relaxedProducer (slot : Zig.Ptr) : Zig.ConcM Tgt Unit :=
  ((do
    match ← Zig.callMC (Zig.Allocator.create ⟨⟩ 4 4) with
    | .error _ => pure ()
    | .ok n =>
      Zig.store (α := BitVec 32) 4 n (42 : BitVec 32)
      Zig.atomicStorePtrC (α := Option Zig.Ptr) .relaxed 8 slot (some n)) :
    Zig.CM Tgt Unit Unit).run' ()

def relaxedDispatch : Tgt → Zig.ConcM Tgt Unit
  | .producer s => relaxedProducer s

/-- `main`, destroying the node it read before the join. -/
def earlyFree : Zig.ConcM Tgt (BitVec 32) := do
  let slot ← Zig.allocStack 8 8
  let r ← ((do
    Zig.store (α := Option Zig.Ptr) 8 slot none
    match ← Zig.spawnC (Tgt.producer slot) with
    | .error _ => pure (0 : BitVec 32)
    | .ok h =>
      let r ← ((match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .acquire 8 slot with
        | some p => do
          let v ← Zig.load (BitVec 32) 4 p
          Zig.callMC (Zig.Allocator.destroy ⟨⟩ 4 p)
          pure v
        | none => pure 0) : Zig.CM Tgt Unit (BitVec 32))
      Zig.joinC h
      ((match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .relaxed 8 slot with
        | some p => Zig.callMC (Zig.Allocator.destroy ⟨⟩ 4 p)
        | none => pure ()) : Zig.CM Tgt Unit Unit)
      pure r) : Zig.CM Tgt Unit (BitVec 32)).run' ()
  Zig.free slot
  pure r

/-- Sampled schedules: constant choices and short periodic patterns. -/
def oracles : List (Nat → Nat) :=
  [fun _ => 0, fun _ => 1, fun _ => 2, fun i => i % 2, fun i => (i + 1) % 2, fun i => i % 3,
   fun i => if i < 4 then 1 else 0, fun i => if i < 8 then 1 else 0, fun i => i / 2 % 2,
   fun i => if i < 2 then 0 else 1, fun i => if i < 6 then 0 else 1]

def outcomes (d : Tgt → Zig.ConcM Tgt Unit) (m : Zig.ConcM Tgt (BitVec 32)) :
    List (Option (Except Error (BitVec 32))) :=
  oracles.map fun o => ((Sched.run ⟨.any, .available⟩ d 200 o m mem0).run).map (·.map (·.1))

def isError : Option (Except Error (BitVec 32)) → Bool
  | some (.error _) => true
  | _ => false

def isIllegal : Option (Except Error (BitVec 32)) → Bool
  | some (.error .illegal) => true
  | _ => false

def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do
    IO.eprintln s!"C09_MUTANT: {message}"
    IO.Process.exit 85

def main : IO Unit := do
  let base := outcomes dispatch publishRead
  require (!base.any isError) "the unmutated client has an error on a sampled schedule"
  require (base.any (· == some (.ok 42))) "the unmutated client never reads the published node"
  require ((outcomes relaxedDispatch publishRead).any isIllegal)
    "relaxed-pointer-publish: the read of the node after a relaxed publish was not rejected with illegal"
  require ((outcomes dispatch earlyFree).any isIllegal)
    "free-before-join: destroying the node before the join was not rejected with illegal"
  IO.println "pointer-atomics mutants: relaxed-pointer-publish and free-before-join rejected"
