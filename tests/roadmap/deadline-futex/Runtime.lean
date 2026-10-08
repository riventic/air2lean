import ZigLean.Conc.TimedSched

open Zig Zig.TimedSched

deriving instance DecidableEq for Except

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"C04_ASSERTION: {name}: expected {reprStr expected}, got {reprStr actual}")

private def ten : Time.Timestamp := ⟨10, by decide⟩
private def eleven : Time.Timestamp := ⟨11, by decide⟩
private def maxTime : Time.Timestamp := ⟨Time.limit - 1, by decide⟩
private def noCancellation : Time.NoCancellation := ⟨fun _ => false, fun _ => rfl⟩
private def equalClock : Time.AwakeEnvironment := ⟨fun _ => ten, fun _ _ _ => Nat.le_refl _⟩
private def advancingClock : Time.AwakeEnvironment where
  observe i := if i = 0 then ten else eleven
  monotonic := by
    intro i j hij
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · simp [hi, hj]
    · simp [hi, hj, ten, eleven]
    · omega
    · simp [hi, hj]

private def input (clock : Time.AwakeEnvironment := equalClock) : Inputs :=
  { environment := .awake clock noCancellation }

private def p : Ptr := ⟨some 0, 0⟩
private def other : Ptr := ⟨some 1, 0⟩
private def memory : Mem :=
  { blocks := #[{ bytes := #[.int 0, .int 0, .int 0, .int 0], align := 4,
                   kind := .stack, live := true, addr := 4096 },
                { bytes := #[.int 73], align := 1,
                   kind := .constGlobal, live := true, addr := 4104 }] }

private def wait (deadline : Time.Timestamp := eleven) (expected : BitVec 32 := 0) : Program Nat :=
  .wait p expected (.deadline deadline) (fun _ => .done 73)

private def clean (s : State α) : Bool :=
  s.kernel.registration.isNone && !(s.kernel.mem.waiters.any (·.1 == 0)) &&
    !(s.kernel.mem.woken.contains 0)

private def result (out : Outcome Nat) : Option (Except Error Nat) := out.result

def main : IO Unit := do
  check "negative/oversized adapter values cannot construct timestamps"
    ((Time.Timestamp.ofNat Time.limit).isNone) true
  check "largest nonnegative i96 timestamp admitted"
    ((Time.Timestamp.ofNat (Time.limit - 1)).isSome) true
  check "duration overflow rejected" ((Time.Timeout.duration eleven).resolve maxTime).isNone true
  check "zero duration preserves current deadline"
    (((Time.Timeout.duration ⟨0, by decide⟩).resolve ten).bind id |>.map (·.nanoseconds)) (some 10)
  check "default no-clock is an unsupported timer"
    (result (run {} 5 (fun _ => 0) (.observe (fun _ => .done 1)) memory))
    (some (.error .unsupportedTimer))
  let mismatch := run (input) 5 (fun _ => 0) (wait eleven 1) memory
  check "predicate mismatch returns normally" (result mismatch) (some (.ok 73))
  check "mismatch leaves no registration" (clean mismatch.state) true
  let expired := run (input) 5 (fun _ => 0) (wait ten) memory
  check "equal deadline returns normally" (result expired) (some (.ok 73))
  check "timeout not source error or boolean" expired.state.reasons #[.timeout]
  check "equal deadline cleanup" (clean expired.state) true
  let pending := run (input) 1 (fun _ => 0) (wait) memory
  check "enqueued call has no result" (result pending) none
  check "continuation actually paused" (match pending.state.control with | .waiting _ => true | _ => false) true
  check "registration retained" pending.state.kernel.registration.isSome true
  check "queue contains selected owner" pending.state.kernel.mem.waiters #[(0, p)]
  check "compare recorded atomic read" (pending.state.kernel.mem.footprint.map (·.kind)) #[.atomicRead]
  check "sentinel unchanged" (pending.state.kernel.mem.blocks[1]?.map (·.bytes)) (some #[.int 73])
  let idle := resume (fun _ => 0) 20 pending.state
  check "equal clock never requires advancement" (result idle) none
  check "fuel exhaustion retains registration" idle.state.kernel.registration.isSome true
  check "equal observations accepted" (idle.state.now.map (·.nanoseconds)) (some 10)
  let spurious := step pending.state (.normal .spurious)
  check "spurious resumes without completing continuation" (result spurious) none
  check "spurious cleanup" (clean spurious.state) true
  check "spurious Unit continuation later completes"
    (result (resume (fun _ => 0) 1 spurious.state)) (some (.ok 73))
  let timeoutPending := run (input advancingClock) 1 (fun _ => 0) (wait) memory
  let observed := step timeoutPending.state .observe
  let timed := step observed.state (.normal .timeout)
  check "later observation enables timeout" timed.state.reasons #[.timeout]
  check "timeout removes registration" (clean timed.state) true
  check "timeout no acquire edge" timed.state.kernel.mem.clocks timeoutPending.state.kernel.mem.clocks
  let tiedInputs := { input advancingClock with wakeAt := fun i => if i = 1 then some (p, 1) else none }
  let tied := step (run tiedInputs 1 (fun _ => 0) (wait) memory).state .observe
  check "boundary wake enabled" (tied.state.kernel.enabled tied.state.now .wake) true
  check "boundary expiry independently enabled" (tied.state.kernel.enabled tied.state.now .timeout) true
  for reason in [ReturnReason.wake, .timeout, .spurious] do
    let returned := step tied.state (.normal reason)
    check "all boundary reasons clean" (clean returned.state) true
    check "all boundary reasons same source Unit"
      (result (resume (fun _ => 0) 1 returned.state)) (some (.ok 73))
    check "normal return leaves sentinel" (returned.state.kernel.mem.blocks[1]?.map (·.bytes)) (some #[.int 73])
    check "normal return adds no access" returned.state.kernel.mem.footprint.size 1
    check "normal return adds no acquire" returned.state.kernel.mem.clocks tied.state.kernel.mem.clocks
  let woke := { pending.state with kernel := pending.state.kernel.wake p 1 }
  check "wake before expiry enabled" (woke.kernel.enabled woke.now .wake) true
  check "wake before expiry timeout disabled" (woke.kernel.enabled woke.now .timeout) false
  let wakeReturn := step woke (.normal .wake)
  check "wake marker consumed" (clean wakeReturn.state) true
  let laterWake := { wakeReturn.state with kernel := wakeReturn.state.kernel.wake p 1 }
  check "later wake cannot resurrect registration" (clean laterWake) true
  let repeatedWait : Program Nat := .wait p 0 (.deadline eleven) (fun _ => wait)
  let first := run (input) 1 (fun _ => 0) repeatedWait memory
  let firstReturn := step { first.state with kernel := first.state.kernel.wake p 1 } (.normal .wake)
  let second := resume (fun _ => 0) 1 firstReturn.state
  check "next wait registers without stale wake" second.state.kernel.mem.waiters #[(0, p)]
  check "next wait stays blocked" (result second) none
  let framed := { pending.state with kernel := { pending.state.kernel with
    mem := { pending.state.kernel.mem with waiters := #[(0, p), (1, other)], woken := #[1, 0, 0] } } }
  let framedReturn := step framed (.normal .spurious)
  check "other owner's waiter framed" framedReturn.state.kernel.mem.waiters #[(1, other)]
  check "other owner's wake framed; duplicates cleared" framedReturn.state.kernel.mem.woken #[1]
  let nullWait : Program Nat := .wait ⟨none, 0⟩ 0 (.deadline eleven) (fun _ => .done 1)
  check "invalid pointer rejected" (result (run (input) 5 (fun _ => 0) nullWait memory))
    (some (.error .illegal))
  let plainRace := { memory with
    clocks := #[#[0, 0], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := #[{ tid := 1, clock := #[0, 1], block := 0, off := 0, len := 4, kind := .write }] }
  check "kernel compare rejects concurrent plain writer"
    (result (run (input) 5 (fun _ => 0) (wait ten) plainRace)) (some (.error .illegal))
  let atomicRace := { plainRace with footprint := plainRace.footprint.map fun e => { e with kind := .atomicWrite } }
  check "kernel compare permits concurrent atomic writer"
    (result (run (input) 5 (fun _ => 0) (wait ten) atomicRace)) (some (.ok 73))
  let readSentinel : Program Nat := Program.liftMem (do
    let bytes ← loadBytes other 1 1
    let value ← intOfBytes 8 bytes
    pure value.toNat)
  check "MemM lift returns actual sentinel bytes"
    (result (run (input) 3 (fun _ => 0) readSentinel memory)) (some (.ok 73))
  let checkedMemory : Program Nat := Program.liftMem (do
    let _ ← loadBytes ⟨none, 0⟩ 1 1
    pure 7)
  check "MemM lift propagates access error"
    (result (run (input) 3 (fun _ => 0) checkedMemory memory)) (some (.error .illegal))
  let divergentMemory : MemM Nat := fun _ => ExceptT.mk none
  let divergent := run (input) 3 (fun _ => 0) (Program.liftMem divergentMemory) memory
  check "MemM no-result remains no-result" (result divergent) none
  check "MemM no-result does not pretend to be waiting"
    (match divergent.state.control with | .running _ => true | _ => false) true
  let changedMemory : Program Nat := Program.liftMem (do
    modify fun m => { m with allocs := 9 }
    pure 7)
  let changed := run (input) 3 (fun _ => 0) changedMemory memory
  check "MemM lift propagates actual memory" changed.state.kernel.mem.allocs 9
  check "MemM lift propagates normal value" (result changed) (some (.ok 7))
  let wakeThenYield : Program Nat :=
    .wake p 1 (fun _ => .yield (fun _ => .done 73))
  let boundWake := wakeThenYield >>= fun value => Program.done (value + 1)
  let wakeMem := { memory with waiters := #[(1, p)] }
  let wakeResult := run (input) 4 (fun _ => 0) boundWake wakeMem
  check "suspended wake/yield bind retains source value" (result wakeResult) (some (.ok 74))
  check "suspended wake/yield preserves scheduler turns" wakeResult.state.trace #[1, 1, 1]
  check "suspended wake/yield delegates queue wake" wakeResult.state.kernel.mem.woken #[1]
  IO.println "C04 opt-in timed scheduler regressions passed"
