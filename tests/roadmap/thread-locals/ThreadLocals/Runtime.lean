import ThreadLocals.Gen

/-! Sampled runtime schedules of the retained translation and two semantic mutants (bounded
evidence; the theorems over all schedules are in `Counters.lean` and `Leak.lean`). -/

open Zig ThreadLocals

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def okValue (r : Option (Except Error (Except ErrName (BitVec 32) × Mem))) : Option Nat :=
  match r with
  | some (.ok (.ok n, _)) => some n.toNat
  | _ => none

private def illegal (r : Option (Except Error (Except ErrName (BitVec 32) × Mem))) : Bool :=
  match r with
  | some (.error .illegal) => true
  | _ => false

/-- Mutant: every worker uses the main thread's instance (no per-thread instances). -/
private def sharedDispatch : Tgt → ConcM Tgt Unit
  | .bumpTwice a => do
    ConcM.liftMem (modify fun m : Mem => m.setTls m.current #[(0, 0)])
    discard (ConcM.liftMem (bumpTwice a))
  | .leak a => discard (ConcM.liftMem (leak a))

/-- Mutant: instances outlive their thread (no `tlsExit`). -/
private def immortalDispatch : Tgt → ConcM Tgt Unit
  | .bumpTwice a => do
    ConcM.liftMem (tlsEnter tlsInit)
    discard (ConcM.liftMem (bumpTwice a))
  | .leak a => do
    ConcM.liftMem (tlsEnter tlsInit)
    discard (ConcM.liftMem (leak a))

def main : IO Unit := do
  for seed in List.range 16 do
    let oracle := fun turn => seed + turn * 7
    require (okValue (Sched.run dispatch 200 oracle twoCounters (mem0 .fresh)).run == some 90908)
      s!"twoCounters failed at schedule {seed}"
    require (illegal (Sched.run dispatch 200 oracle leaked (mem0 .fresh)).run)
      s!"leaked pointer read did not throw .illegal at schedule {seed}"
    -- Shared instances: the workers' increments race with each other or with main.
    require (okValue (Sched.run sharedDispatch 200 oracle twoCounters (mem0 .fresh)).run != some 90908)
      s!"shared-instance mutant still returned 90908 at schedule {seed}"
    -- Immortal instances: the leaked read succeeds and reads the worker's 7.
    require (okValue (Sched.run immortalDispatch 200 oracle leaked (mem0 .fresh)).run == some 7)
      s!"immortal-instance mutant did not read the worker's instance at schedule {seed}"
  IO.println "thread-local runtime schedules and mutants passed"
