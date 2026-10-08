import DeadlineActual.Gen
import ZigLean.Conc.TimedCompare

/-! ROOT-only checks of the entire actual emitted module. No exported function body
is reproduced here. This is interpreter qualification, not OS-clock conformance or
the pending source atomic-read coherence correspondence. -/
open Zig

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"C04_GENERATED: {message}")

private def ten : Time.Timestamp := ⟨10, by decide⟩
private def policy : Time.NoCancellation := ⟨fun _ => false, fun _ => rfl⟩
private def clock : Time.AwakeEnvironment := ⟨fun _ => ten, fun _ _ _ => Nat.le_refl _⟩
private def inputs : TimedSched.Inputs := { environment := .awake clock policy }

private def allocateWord : MemM Ptr := do
  let p ← allocStack 4 4
  store 4 p (BitVec.ofNat 32 0)
  return p

def main : IO Unit := do
  let some (.ok (p, memory)) := (allocateWord.run DeadlineActual.mem0).run
    | throw (IO.userError "C04_GENERATED: word preparation failed")
  let observed := TimedSched.run inputs 80 (fun _ => 0) (DeadlineActual.observe {}) memory
  require (match observed.result with | some (.ok n) => n == 10 | _ => false)
    "actual observe body did not return the selected clock"
  let zero := TimedSched.run inputs 80 (fun _ => 0) (DeadlineActual.waitZero {} p 0) memory
  require (match zero.result with | some (.ok (.ok ())) => true | _ => false)
    "actual zero-duration body did not return Unit success"
  let pending := TimedSched.run inputs 80 (fun _ => 0)
    (DeadlineActual.waitDeadline {} p 0 (BitVec.ofNat 96 11)) memory
  require (pending.result.isNone && pending.state.kernel.registration.isSome)
    "actual future-deadline body did not stay paused"
  let released := TimedSched.step pending.state (.normal .spurious)
  let complete := TimedSched.resume (fun _ => 0) 80 released.state
  require (match complete.result with | some (.ok (.ok ())) => true | _ => false)
    "actual wait continuation did not resume with source Unit success"
  require (complete.state.kernel.registration.isNone && complete.state.kernel.mem.waiters.isEmpty &&
    complete.state.kernel.mem.woken.isEmpty) "actual wait continuation leaked registration"
  let boundary := TimedSched.run inputs 160 (fun _ => 0)
    (DeadlineActual.boundaryClient {}) DeadlineActual.mem0
  require (match boundary.result with | some (.ok (.ok n)) => n == 73 | _ => false)
    "actual boundaryClient body did not propagate successful return"
  let noClock := TimedSched.run {} 80 (fun _ => 0) (DeadlineActual.observe {}) memory
  require (match noClock.result with | some (.error .unsupportedTimer) => true | _ => false)
    "actual generated body acquired a clock in the default environment"

  -- Two readable source messages: option 0 is current, option 1 is older.
  let some block := p.block | throw (IO.userError "C04_GENERATED: missing word block")
  let prior : Msg := { id := 100, bytes := Enc.encode (BitVec.ofNat 32 7), clock := #[], relClock := #[] }
  let current : Msg := { id := 101, bytes := Enc.encode (BitVec.ofNat 32 0), clock := #[0, 1], relClock := #[] }
  let history := { memory with atomics := #[{ block, off := 0, len := 4, msgs := #[prior, current] }], nextMsg := 102, seen := #[] }
  let oldInputs := { inputs with readChoice := fun _ => 1 }
  let older := TimedSched.run oldInputs 80 (fun _ => 0)
    (DeadlineActual.waitDeadline {} p 0 (BitVec.ofNat 96 11)) history
  require (match older.result with | some (.ok (.ok ())) => true | _ => false)
    "selected older message did not cause mismatch normal return"
  require (older.state.kernel.mem.seen.contains (history.current, 0, 100))
    "selected older compare did not retain seen message id"
  let newest := TimedSched.run inputs 80 (fun _ => 0)
    (DeadlineActual.waitDeadline {} p 0 (BitVec.ofNat 96 11)) history
  require (newest.result.isNone && newest.state.kernel.registration.isSome &&
    newest.state.kernel.mem.seen.contains (history.current, 0, 101))
    "selected current message did not pause and retain seen message id"
  let floorMemory := { history with seen := #[(history.current, 0, 101)] }
  let forbidden := TimedSched.run oldInputs 80 (fun _ => 0)
    (DeadlineActual.waitDeadline {} p 0 (BitVec.ofNat 96 11)) floorMemory
  require (match forbidden.result with | some (.error .illegal) => true | _ => false)
    "seen floor accepted an unavailable older read choice"
