import ZigLean.Time
import ZigLean.Mem.Thread

/-!
Opt-in executable timed-wait foundation for one selected caller and environment wake
events. It is not imported by ZigLean.Conc and has no translator adapter. The existing
SyncOp, Sched.run and their protocol proofs are unchanged.

The caller's continuation remains paused while registered. Environment observations,
normal spurious return, wake and expiry compete through an oracle; equal observations
and runs with no result are permitted. No normal return adds an acquire edge. The caller
must recheck its predicate and time, and discharge task lifetime separately.
-/
namespace Zig.TimedSched

inductive ReturnReason where
  | mismatch | wake | timeout | spurious
  deriving DecidableEq, Repr

structure Registration where
  owner : ThreadId
  pointer : Ptr
  deadline : Option Time.Timestamp

structure Kernel where
  mem : Mem
  registration : Option Registration := none

/-- One existing relaxed atomic-read event. The explicit readable-option index keeps
location creation, coherent read choices and the selected message's seen floor. -/
def readWord (readChoice : Nat) (p : Ptr) : MemM (BitVec 32) :=
  atomicLoadAt readChoice .relaxed 4 p

/-- Reject overlap with an existing wait of this caller. Other owners are framed. -/
def Kernel.begin (s : Kernel) (readChoice : Nat) (p : Ptr) (expected : BitVec 32)
    (deadline : Option Time.Timestamp) (now : Time.Timestamp) :
    Result (Option ReturnReason × Kernel) := do
  if s.registration.isSome || s.mem.waiters.any (·.1 == s.mem.current) ||
      s.mem.woken.contains s.mem.current then throw .illegal
  let (word, m) ← (readWord readChoice p).run s.mem
  if word ≠ expected then return (some .mismatch, { s with mem := m })
  if deadline.any (fun expiry => expiry.nanoseconds ≤ now.nanoseconds) then
    return (some .timeout, { s with mem := m })
  let r : Registration := ⟨m.current, p, deadline⟩
  return (none, { mem := { m with waiters := m.waiters.push (r.owner, p) },
                  registration := some r })

/-- Wake changes queue bookkeeping only; it supplies no happens-before edge. The timed kernel
serves one registration per owner and wakes in queue order (no oracle choice of waiters, unlike
`Sched`). -/
def Kernel.wake (s : Kernel) (p : Ptr) (n : Nat) : Kernel :=
  match h : ((Thread.futexWake p n []).run s.mem).run with
  | some (.ok (_, mem)) => { s with mem := mem }
  | some (.error _) => by cases h
  | none => by cases h

def Kernel.enabled (s : Kernel) (now : Option Time.Timestamp) : ReturnReason → Bool
  | .mismatch => false
  | .spurious => s.registration.isSome
  | .wake => s.registration.any (fun r => s.mem.woken.contains r.owner)
  | .timeout => s.registration.any fun r =>
      r.deadline.any fun expiry => now.any (fun t => expiry.nanoseconds ≤ t.nanoseconds)

/-- Every accepted normal return removes the selected registration and all its wake
markers. It leaves the other owners' entries and the entire source memory unchanged. -/
def Kernel.release (s : Kernel) : Kernel :=
  match s.registration with
  | none => s
  | some r =>
    { mem := { s.mem with
        waiters := s.mem.waiters.filter (fun w => w.1 != r.owner),
        woken := s.mem.woken.filter (fun t => t != r.owner) },
      registration := none }

/-- A finite interactive program, separate from translated ConcM. Source-visible wait
success is Unit; the internal reason is not passed to the continuation. -/
inductive Program (α : Type) where
  | done (value : α)
  | fail (error : Error)
  | observe (next : Time.Timestamp → Program α)
  | memory {β : Type} (action : MemM β) (next : β → Program α)
  | wait (pointer : Ptr) (expected : BitVec 32) (timeout : Time.Timeout)
      (next : Unit → Program α)
  | wake (pointer : Ptr) (count : Nat) (next : Unit → Program α)
  | yield (next : Unit → Program α)

def Program.bind (program : Program α) (f : α → Program β) : Program β :=
  match program with
  | .done a => f a
  | .fail e => .fail e
  | .observe next => .observe fun now => (next now).bind f
  | .memory action next => .memory action fun value => (next value).bind f
  | .wait p e timeout next => .wait p e timeout fun u => (next u).bind f
  | .wake p n next => .wake p n fun u => (next u).bind f
  | .yield next => .yield fun u => (next u).bind f

instance : Monad Program where
  pure := .done
  bind := Program.bind

def Program.liftMem (action : MemM α) : Program α := .memory action .done

inductive Control (α : Type) where
  | running (program : Program α)
  | waiting (next : Unit → Program α)

structure Inputs where
  environment : Time.Environment := Time.defaultEnvNoClock
  /-- A wake at the same boundary as this actual observation. No source write or task
  completion is implied. Boundary wake and expiry may both become enabled. -/
  wakeAt : Nat → Option (Ptr × Nat) := fun _ => none
  /-- Readable-option index for each attempted timed comparison, not a message id.
  Invalid choices retain atomicLoadAt's error; the index is never clamped. -/
  readChoice : Nat → Nat := fun _ => 0

structure State (α : Type) where
  inputs : Inputs
  kernel : Kernel
  control : Control α
  now : Option Time.Timestamp := none
  observations : Nat := 0
  reads : Nat := 0
  choices : Nat := 0
  trace : Array Nat := #[]
  reasons : Array ReturnReason := #[]

/-- A resumable snapshot is retained even when fuel runs out. Errors are model errors;
ordinary source error values can instead be represented in Program's result type. -/
structure Outcome (α : Type) where
  result : Option (Except Error α)
  state : State α

def State.observe (s : State α) : Except Error (Time.Timestamp × State α) :=
  match s.inputs.environment with
  | .noClock => .error .unsupportedTimer
  | .awake env _ =>
    let now := env.observe s.observations
    let kernel := match s.inputs.wakeAt s.observations with
      | none => s.kernel
      | some (p, n) => s.kernel.wake p n
    .ok (now, { s with kernel := kernel, now := some now,
                        observations := s.observations + 1 })

inductive Event where
  | run | observe | normal (reason : ReturnReason)
  deriving Inhabited

/-- Observation is always an option for a blocked timed caller, even with equal time.
Thus a timed queue is never mistaken for a legacy deadlock. No option is fair. -/
def State.events (s : State α) : Array Event :=
  match s.control with
  | .running _ => #[.run]
  | .waiting _ =>
    #[.observe] ++ (#[ReturnReason.spurious, .wake, .timeout].filterMap fun r =>
      if s.kernel.enabled s.now r then some (.normal r) else none)

def resumeNormal (s : State α) (next : Unit → Program α) (reason : ReturnReason) : State α :=
  { s with kernel := s.kernel.release, control := .running (next ()),
           reasons := s.reasons.push reason }

def withObservation (s : State α) (next : Time.Timestamp → State α → Outcome α) : Outcome α :=
  match s.observe with
  | .error error => ⟨some (.error error), s⟩
  | .ok (now, s') => next now s'

/-- A single event. No continuation executes until a normal return is selected. -/
def step (s : State α) (event : Event) : Outcome α :=
  match event, s.control with
  | .observe, .waiting _ => withObservation s fun _ s' => ⟨none, s'⟩
  | .normal r, .waiting next =>
    if s.kernel.enabled s.now r then ⟨none, resumeNormal s next r⟩
    else ⟨some (.error .illegal), s⟩
  | .run, .running program =>
    match program with
    | .done value => ⟨some (.ok value), s⟩
    | .fail error => ⟨some (.error error), s⟩
    | .yield next => ⟨none, { s with control := .running (next ()) }⟩
    | .wake p n next =>
      ⟨none, { s with kernel := s.kernel.wake p n, control := .running (next ()) }⟩
    | .observe next => withObservation s fun now s' =>
      ⟨none, { s' with control := .running (next now) }⟩
    | .memory action next =>
      match (action.run s.kernel.mem).run with
      | none => ⟨none, s⟩
      | some (.error error) => ⟨some (.error error), s⟩
      | some (.ok (value, mem)) =>
        ⟨none, { s with kernel := { s.kernel with mem := mem },
                        control := .running (next value) }⟩
    | .wait p expected timeout next => withObservation s fun now s' =>
        match timeout.resolve now with
        | none => ⟨some (.error .unspecified), s'⟩
        | some deadline =>
          let readChoice := s'.inputs.readChoice s'.reads
          let s' := { s' with reads := s'.reads + 1 }
          match ((s'.kernel.begin readChoice p expected deadline now).run) with
          | none => ⟨none, s'⟩
          | some (.error e) => ⟨some (.error e), s'⟩
          | some (.ok (reason, kernel)) =>
            let s' := { s' with kernel := kernel }
            match reason with
            | some r => ⟨none, resumeNormal s' next r⟩
            | none => ⟨none, { s' with control := .waiting next }⟩
  | _, _ => ⟨some (.error .illegal), s⟩

/-- Continue a snapshot with its original selected environment and observation cursor. -/
def resume (oracle : Nat → Nat) : Nat → State α → Outcome α
  | 0, s => ⟨none, s⟩
  | fuel + 1, s =>
    let options := s.events
    let event := options[oracle s.choices % options.size]!
    let s := { s with choices := s.choices + 1, trace := s.trace.push options.size }
    let out := step s event
    match out.result with
    | some _ => out
    | none => resume oracle fuel out.state

def run (inputs : Inputs) (fuel : Nat) (oracle : Nat → Nat) (program : Program α)
    (mem : Mem := {}) : Outcome α :=
  resume oracle fuel { inputs := inputs, kernel := { mem := { mem with current := 0 } },
                              control := .running program }

end Zig.TimedSched
