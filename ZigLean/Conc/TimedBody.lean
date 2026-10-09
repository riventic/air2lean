import ZigLean.Conc.TimedCall

/-! Explicit effect lifts for the acyclic selected emitter. No catch or fixed-point
instance is provided; unsupported control flow must be rejected before emission. -/
namespace Zig.TimedBody

abbrev TM (σ α : Type) := StateT σ TimedSched.Program α

/-- Execute one existing memory-body operation while retaining its updated locals.
The memory action remains an interpreter node, so errors/no-result retain its snapshot. -/
def callBody (action : MM σ α) : TM σ α := fun locals =>
  TimedSched.Program.liftMem (action.run locals)

def callProgram (action : TimedSched.Program α) : TM σ α := StateT.lift action

def fail (error : Error) : TM σ α := StateT.lift (.fail error)

def observeClock (awake : Bool) (construct : BitVec 96 → α) : TimedSched.Program α :=
  if awake then .observe fun now => .done (construct (BitVec.ofNat 96 now.nanoseconds))
  else .fail .unsupportedTimer

def waitTimeout (p : Ptr) (expected : BitVec 32) (timeout : Option Time.Timeout) :
    TimedSched.Program (Except ErrName Unit) :=
  match timeout with
  | none => .fail .unsupportedTimer
  | some selected => .wait p expected selected (fun _ => .done (.ok ()))

end Zig.TimedBody
