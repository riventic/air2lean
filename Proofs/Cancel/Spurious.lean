import ZigLean.Conc.Sched
import ZigLean.Conc.Call

/-!
# Spurious futex returns: a client that rechecks and one that does not (C05)

`std.Io.futexWait`, `std.Io.futexWaitUncancelable` and `std.Thread.Futex.wait` may return
spuriously (Zig 0.16.0 `lib/std/Io.zig:1540-1549`: "a spurious ("random") wakeup occurs ... The
caller is responsible for identifying spurious wakeups if necessary, typically by checking the
value at `ptr.*`"; the threaded backend returns on `EINTR`, `lib/std/Io/Threaded.zig:1022`).
The scheduler offers this outcome at every wait that would sleep (`Sched.spuriousWake`, the
oracle's option 1; option 0 sleeps).

Both clients below have the same shape: `main` makes a word `flag = 0`, spawns `setter`, which
stores `1` with a release and wakes one waiter, waits for the flag, reads it with an acquire and
returns what it read after joining `setter`. The postcondition is "the result is `1`".

- `waitOnce` waits once and does not recheck. `waitOnce_spurious` is a schedule that violates the
  postcondition: `main` returns spuriously before `setter` ran and reads `0`. With the oracle that
  never returns spuriously the same client gives `1` (`waitOnce_sleep`).
- `waitLoop` rechecks the flag before every wait (`while (flag.load(.acquire) == 0)
  io.futexWait(...)`), bounded by `rounds` so the kernel can run it. Under the spurious schedule
  of `waitOnce` it gives `1` (`waitLoop_spurious`), as under a sleeping schedule
  (`waitLoop_sleep`) and two more spurious returns (`waitLoop_spurious_twice`).

These are kernel computations of single schedules (`decide +kernel`); the negative needs only one.
The all-schedules statements for the std clients that recheck under spurious returns are the
rebuilt proofs of `Proofs/Sync/Semaphore.lean`, `Proofs/Sync/Handoff.lean`,
`Proofs/Sync/RwLock.lean`, `Proofs/Sync/Mutex.lean`, `Proofs/Threadsync/*` and
`Proofs/Iogroup/Counter.lean`, whose futex rules (`WP.futexWaitC`) now quantify over the spurious
return. `tests/roadmap/cancellation/Runtime.lean` samples many schedules of both clients.
-/

open Zig

namespace Cancel.Spurious

/-- The one spawn target: `setter(flag)`. -/
inductive Tgt where
  | setter (flag : Ptr)

/-- `flag.store(1, .release); io.futexWake(u32, &flag, 1)`. -/
def setter (flag : Ptr) : ConcM Tgt Unit :=
  (do
    atomicStoreC (n := 32) .release 4 flag 1
    futexWakeC ⟨⟩ flag 1 : CM Tgt Unit Unit).run' ()

def dispatch : Tgt → ConcM Tgt Unit
  | .setter flag => setter flag

/-- A new word `0` and the spawn of `setter`. -/
def start : CM Tgt Unit (Ptr × ThreadId) := do
  let flag ← callMC (alloc .heap 4 4)
  callMC (store 4 flag (0 : BitVec 32))
  let tid ← spawnC (Tgt.setter flag)
  match tid with
  | .ok tid => pure (flag, tid)
  | .error _ => callRC (throw .unspecified)

/-- The end: read the flag, join `setter`, free the word. -/
def finish (flag : Ptr) (tid : ThreadId) : CM Tgt Unit (BitVec 32) := do
  let v ← atomicLoadC (n := 32) .acquire 4 flag
  joinC tid
  callMC (free flag)
  pure v

/-- Negative: one futex wait, no recheck of the flag. -/
def waitOnce : ConcM Tgt (BitVec 32) :=
  (do
    let (flag, tid) ← start
    futexWaitC ⟨⟩ flag (0 : BitVec 32)
    finish flag tid : CM Tgt Unit (BitVec 32)).run' ()

/-- At most `rounds` rechecks: load the flag; while it is `0`, wait. -/
def recheck (flag : Ptr) : Nat → CM Tgt Unit Unit
  | 0 => pure ()
  | rounds + 1 => do
    let v ← atomicLoadC (n := 32) .acquire 4 flag
    if v = 0 then
      futexWaitC ⟨⟩ flag (0 : BitVec 32)
      recheck flag rounds

/-- Positive: the flag is rechecked before every wait. -/
def waitLoop (rounds : Nat) : ConcM Tgt (BitVec 32) :=
  (do
    let (flag, tid) ← start
    recheck flag rounds
    finish flag tid : CM Tgt Unit (BitVec 32)).run' ()

/-- The value of a run, if it gave one. -/
def valueOf (r : Result (BitVec 32 × Mem)) : Option (BitVec 32) :=
  match r.run with
  | some (.ok (v, _)) => some v
  | _ => none

/-- The oracle that follows `xs`, then takes option 0. -/
def follow (xs : List Nat) : Nat → Nat := fun i => xs.getD i 0

/-- Every choice is option 0: a wait that would sleep sleeps. -/
def never : Nat → Nat := fun _ => 0

/-- The spurious schedule. Choice 0 has one option (only `main` can go on); choice 1 picks
`main` (at its wait) over `setter`; choice 2 is the wait's two options, sleep or the spurious
return (`Sched.spuriousWake`), and takes the spurious return before `setter` stored. -/
def spurious : Nat → Nat := follow [0, 0, 1]

theorem waitOnce_sleep : valueOf (Sched.run dispatch 40 never waitOnce {}) = some 1 := by
  decide +kernel

/-- The negative: a spurious return lets `waitOnce` read `0`, which violates "the result is
`1`". -/
theorem waitOnce_spurious : valueOf (Sched.run dispatch 40 spurious waitOnce {}) = some 0 := by
  decide +kernel

theorem waitLoop_sleep : valueOf (Sched.run dispatch 60 never (waitLoop 4) {}) = some 1 := by
  decide +kernel

theorem waitLoop_spurious : valueOf (Sched.run dispatch 60 spurious (waitLoop 4) {}) = some 1 := by
  decide +kernel

/-- Two spurious returns in a row, then a sleep. -/
theorem waitLoop_spurious_twice :
    valueOf (Sched.run dispatch 60 (follow [0, 0, 1, 0, 0, 0, 1]) (waitLoop 4) {}) = some 1 := by
  decide +kernel

end Cancel.Spurious
