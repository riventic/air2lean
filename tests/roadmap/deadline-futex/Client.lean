import ZigLean.Conc.TimedClient

open Zig

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"C04_CLIENT: {message}")

private def ten : Time.Timestamp := ⟨10, by decide⟩
private def eleven : Time.Timestamp := ⟨11, by decide⟩
private def policy : Time.NoCancellation := ⟨fun _ => false, fun _ => rfl⟩
private def clock : Time.AwakeEnvironment := ⟨fun _ => ten, fun _ _ _ => Nat.le_refl _⟩
private def inputs : TimedSched.Inputs := { environment := .awake clock policy }

private def advance (state : TimedSched.State α) (count : Nat) : TimedSched.State α :=
  (List.range count).foldl (fun s _ => (TimedSched.step s .run).state) state

def main : IO Unit := do
  let program := TimedClient.attempt {} 0 0 eleven
  -- Allocation, two stores, then wait registration; the continuation must pause.
  let pending := TimedSched.run inputs 4 (fun _ => 0) program
  require pending.result.isNone "client completed before return event"
  require pending.state.kernel.registration.isSome "client did not register"
  require (pending.state.kernel.mem.blocks.size == 1 &&
    (pending.state.kernel.mem.blocks[0]?).any (fun block => block.live))
    "waiting client lost its owned block"
  let released := TimedSched.step pending.state (.normal .spurious)
  -- Predicate load, clock observation, sentinel load, free, then done.
  let complete := TimedSched.step (advance released.state 4) .run
  require (match complete.result with
    | some (.ok receipt) => receipt.status == .retry && receipt.sentinel == 73
    | _ => false) "spurious predeadline return did not recheck and retry"
  require ((complete.state.kernel.mem.blocks[0]?).any (fun block => !block.live) &&
    complete.state.kernel.registration.isNone && complete.state.kernel.mem.waiters.isEmpty &&
    complete.state.kernel.mem.woken.isEmpty) "normal client return leaked lifetime state"
  let expired := TimedSched.run inputs 20 (fun _ => 0) (TimedClient.attempt {} 0 0 ten)
  require (match expired.result with
    | some (.ok receipt) => receipt.status == .expired && receipt.sentinel == 73
    | _ => false) "equal deadline was not expired"
  let changed := TimedSched.run inputs 20 (fun _ => 0) (TimedClient.attempt {} 1 0 ten)
  require (match changed.result with
    | some (.ok receipt) => receipt.status == .changed && receipt.sentinel == 73
    | _ => false) "mismatch predicate did not take priority over expiry"
