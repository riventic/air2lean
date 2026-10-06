import ZigLean.Conc.TimedCall

/-!
Unqualified executable client candidate for the selected timed interpreter. This is
not emitted code and is not a correspondence theorem for std.Io. The caller owns its
word and sentinel; the environment may wake it but has no source-memory write action.
A normal wait return always rechecks the predicate and clock. One attempt can return
retry, so this example supplies neither eventual completion nor fairness.
-/
namespace Zig.TimedClient

inductive Status where
  | changed | expired | retry
  deriving DecidableEq, Repr

structure Receipt where
  status : Status
  sentinel : BitVec 32
  deriving DecidableEq, Repr

/-- One bounded attempt, with reclamation after each successful source return.
Model errors and paused/no-result outcomes do not assert that cleanup has happened;
their snapshot retains the allocation and, while waiting, the paused continuation.
The predicate uses an ordinary tracked load under the absence-of-writers scope.
Kernel atomic-read coherence with the source RC11 model remains unqualified. -/
def attempt (io : Io) (initial expected : BitVec 32) (deadline : Time.Timestamp) :
    TimedSched.Program Receipt := do
  let base ← TimedSched.Program.liftMem (allocStack 8 4)
  let sentinelPointer := base.add 4
  TimedSched.Program.liftMem (store 4 base initial)
  TimedSched.Program.liftMem (store 4 sentinelPointer (BitVec.ofNat 32 73))
  let returned ← TimedCall.futexWaitTimeout io base expected
    (.deadline { raw := ⟨BitVec.ofNat 96 deadline.nanoseconds⟩, clock := .awake })
  match returned with
  | .error _ => .fail .unspecified
  | .ok () => do
    let word ← TimedSched.Program.liftMem (load (BitVec 32) 4 base)
    let now ← TimedCall.clockNow .awake io
    let sentinel ← TimedSched.Program.liftMem (load (BitVec 32) 4 sentinelPointer)
    TimedSched.Program.liftMem (free base)
    let status := if word ≠ expected then Status.changed
      else if deadline.nanoseconds ≤ now.nanoseconds.toNat then Status.expired
      else Status.retry
    return ⟨status, sentinel⟩

end Zig.TimedClient
