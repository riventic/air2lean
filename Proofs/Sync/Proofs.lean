import Proofs.Sync.Gen

/-!
# Proofs about `examples/sync/sync.zig`

`Io.Mutex` is translated from Zig 0.16.0's std code; the futex under it is the model
(`ZigLean/Conc/Sched.lean`). Its lock has loops (`partial_fixpoint`), which the kernel does not
run, so a spec of `mutexCounter` over all schedules is milestone T4/T5 (`PLAN.md`); the diff test
checks it against the compiled Zig over the schedules. This file has the steps without a loop,
computed by the kernel (`decide +kernel`) under the sequentially consistent schedule, and the
deadlock rule of the model.
-/

open Zig Sync

/-- The schedule that always takes option 0. -/
def sc : Nat → Nat := fun _ => 0

/-- A new mutex (all bytes 0: `.unlocked`) in a stack block. -/
def newMutex : ConcM Tgt Ptr := do
  let p ← ConcM.liftMem (alloc .stack 4 4)
  ConcM.liftMem (store (α := BitVec 32) 4 p 0)
  pure p

/-- `true`/`false` for a statement about a run. -/
def boolOf (r : Result (Bool × Mem)) : Option Bool :=
  match r.run with
  | some (.ok (b, _)) => some b
  | _ => none

/-- `tryLock` of a new mutex takes it. -/
theorem tryLock_new : boolOf (Sched.run dispatch 10 sc (do Io_Mutex_tryLock (← newMutex)) {}) = some true := by
  decide +kernel

/-- A second `tryLock` of a taken mutex fails. -/
theorem tryLock_twice :
    boolOf (Sched.run dispatch 10 sc (do
      let p ← newMutex
      let _ ← Io_Mutex_tryLock p
      Io_Mutex_tryLock p) {}) = some false := by
  decide +kernel

/-- The only thread waits at a futex that no thread wakes: the run is `.deadlock`. -/
theorem wait_alone_deadlock :
    (match (Sched.run dispatch 10 sc (do
      let p ← newMutex
      ConcM.sync (Tgt := Tgt) (.wait p 0)) {}).run with
     | some (.error .deadlock) => true
     | _ => false) = true := by
  decide +kernel

/-- The futex value differs: the wait goes on. -/
theorem wait_other_value :
    (match (Sched.run dispatch 10 sc (do
      let p ← newMutex
      ConcM.sync (Tgt := Tgt) (.wait p 1)) {}).run with
     | some (.ok _) => true
     | _ => false) = true := by
  decide +kernel
