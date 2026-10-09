import IdleLoop.Basic

/-!
# C03 idle loop: semantic mutants of the client

`idle_safe` (every oracle and fuel: no error) is a kernel theorem about the unmutated client.
These bounded runtime witnesses show that it depends on the translated idle loop and on the
release/acquire publication, so the safety proof is not vacuous:

- `idle-loop-skipped`: the worker reads `data` without running the translated idle loop. The
  read races with `main`'s plain write of `data` on some sampled schedule (`.illegal`).
- `relaxed-publish`: `main` stores 1 to `flag` with `.relaxed` instead of `.release`. The worker's
  acquire load can read 1 without synchronizing, so its read of `data` races (`.illegal`).

`Zig.loop` is a `partial_fixpoint`, so the kernel does not reduce these runs: like
`tests/roadmap/shared-reclamation/Runtime.lean` they execute the compiled model over sampled
oracles. The unmutated client has no error on any sampled oracle (a run may run out of fuel).
-/

open Zig IdleLoop.Client

/-- The worker without its idle loop: it reads `data` at once. -/
def skipDispatch : Tgt → ConcM Tgt Unit
  | .worker => check

/-- `main`, publishing `flag` with a relaxed store. -/
def relaxedMain : ConcM Tgt Unit :=
  syncSpawn .worker >>= fun r =>
    let h := match r with | .ok h => h | .error _ => 0
    ConcM.liftMem (store 4 dPtr (42 : BitVec 32)) >>= fun _ =>
      syncPick (storeCount 32 .relaxed 4 fPtr) >>= fun c =>
        ConcM.liftMem (atomicStoreAt c .relaxed 4 fPtr (1 : BitVec 32)) >>= fun _ => syncJoin h

/-- Sampled schedules: constant choices and short periodic patterns. -/
def oracles : List (Nat → Nat) :=
  [fun _ => 0, fun _ => 1, fun i => i % 2, fun i => (i + 1) % 2, fun i => i % 3,
   fun i => if i < 4 then 1 else 0, fun i => if i < 8 then 1 else 0, fun i => i / 2 % 2]

def outcomes (d : Tgt → ConcM Tgt Unit) (m : ConcM Tgt Unit) : List (Option (Except Error Unit)) :=
  oracles.map fun o => ((Sched.run ⟨.any, .available⟩ d 200 o m mem0).run).map (·.map (·.1))

def isError : Option (Except Error Unit) → Bool
  | some (.error _) => true
  | _ => false

def isIllegal : Option (Except Error Unit) → Bool
  | some (.error .illegal) => true
  | _ => false

def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do
    IO.eprintln s!"C03_MUTANT: {message}"
    IO.Process.exit 85

def main : IO Unit := do
  let base := outcomes dispatch IdleLoop.Client.main
  require (!base.any isError) "the unmutated client has an error on a sampled schedule"
  require (base.any (· == some (.ok ()))) "the unmutated client returns on no sampled schedule"
  require ((outcomes skipDispatch IdleLoop.Client.main).any isIllegal)
    "idle-loop-skipped: the read of data without the idle loop was not rejected with illegal"
  require ((outcomes dispatch relaxedMain).any isIllegal)
    "relaxed-publish: a relaxed flag store did not make the read of data race"
  IO.println "C03 idle-loop mutants rejected (idle-loop-skipped, relaxed-publish)"
