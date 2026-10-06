import ZigLean.Conc.TimedCall

open Zig

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"C04_ADAPTER: {message}")

private def ten : Time.Timestamp := ⟨10, by decide⟩
private def eleven : Time.Timestamp := ⟨11, by decide⟩
private def policy : Time.NoCancellation := ⟨fun _ => false, fun _ => rfl⟩
private def clock : Time.AwakeEnvironment := ⟨fun _ => ten, fun _ _ _ => Nat.le_refl _⟩
private def inputs : TimedSched.Inputs := { environment := .awake clock policy }
private def pointer : Ptr := ⟨some 0, 0⟩
private def memory : Mem :=
  { blocks := #[{ bytes := #[.int 0, .int 0, .int 0, .int 0], align := 4,
                   kind := .stack, live := true, addr := 4096 }] }
private def timeout : TimedCall.Timeout :=
  .deadline { raw := ⟨BitVec.ofNat 96 11⟩, clock := .awake }

def main : IO Unit := do
  require (TimedCall.checkedNanoseconds (BitVec.ofInt 96 (-1))).isNone "negative timestamp admitted"
  require (TimedCall.checkedTimeout (.deadline { raw := ⟨0⟩, clock := .real })).isNone
    "wall-clock deadline admitted"
  require (TimedCall.checkedTimeout .none).isNone "unbounded timeout admitted"
  let observed := TimedSched.run inputs 3 (fun _ => 0) (TimedCall.clockNow .awake {}) memory
  require (match observed.result with
    | some (.ok timestamp) => timestamp.nanoseconds == BitVec.ofNat 96 10
    | _ => false) "clock callback result differs"
  let call := TimedCall.futexWaitTimeout {} pointer 0 timeout
  let pending := TimedSched.run inputs 1 (fun _ => 0) call memory
  require pending.result.isNone "timed call returned before a return event"
  require (match pending.state.control with | .waiting _ => true | _ => false)
    "source continuation not paused"
  require pending.state.kernel.registration.isSome "missing registration"
  let normal := TimedSched.step pending.state (.normal .spurious)
  let finished := TimedSched.resume (fun _ => 0) 2 normal.state
  require (match finished.result with | some (.ok (.ok ())) => true | _ => false)
    "normal return not source error-union Unit success"
  require (finished.state.kernel.registration.isNone && finished.state.kernel.mem.waiters.isEmpty &&
    finished.state.kernel.mem.woken.isEmpty) "normal return leaked registration"
  let noClock := TimedSched.run {} 3 (fun _ => 0) (TimedCall.clockNow .awake {}) memory
  require (match noClock.result with | some (.error .unspecified) => true | _ => false)
    "default environment gained a clock"
