import ZigLean.Conc.TimedBudget

/-! Executable C04 named-case regressions for the solver budget path over the selected
timed interpreter: deadline boundary, timeout, wake-before-timeout, wake-at-timeout,
iteration cap, an equal clock that never advances, and budget overflow. -/
open Zig Zig.TimedSched Zig.TimedBudget

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"C04_CASE: {name}: expected {reprStr expected}, got {reprStr actual}")

/-- Comparable view of an outcome: tag, solver state/answer and decision time. -/
private def view : Option (Except Error (Verdict Nat Nat)) → String
  | some (.ok (.solved answer now)) => s!"solved {answer} at {now.nanoseconds}"
  | some (.ok (.expired state now)) => s!"expired {state} at {now.nanoseconds}"
  | some (.ok (.capped state)) => s!"capped {state}"
  | some (.ok .unrepresentable) => "unrepresentable"
  | some (.error _) => "model error"
  | none => "pending"

private def noCancellation : Time.NoCancellation := ⟨fun _ => false, fun _ => rfl⟩

/-- A representable timestamp, saturating at 1000. -/
private def ts (n : Nat) : Time.Timestamp :=
  ⟨min n 1000, Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)⟩

/-- Observation `i` reads `base + i`, saturating at 1000. -/
private def ticking (base : Nat) : Time.AwakeEnvironment where
  observe i := ts (base + i)
  monotonic := by intro i j h; show min (base + i) 1000 ≤ min (base + j) 1000; omega

private def frozen (at_ : Nat) (h : at_ < Time.limit) : Time.AwakeEnvironment :=
  ⟨fun _ => ⟨at_, h⟩, fun _ _ _ => Nat.le_refl _⟩

private def input (clock : Time.AwakeEnvironment)
    (wakeAt : Nat → Option (Ptr × Nat) := fun _ => none) : Inputs :=
  { environment := .awake clock noCancellation, wakeAt := wakeAt }

/-- A solver needing `n + 1` steps: it answers 42 from state 0. -/
private def countdown (n : Nat) : Except Nat Nat := if n = 0 then .ok 42 else .error (n - 1)

private def word : Ptr := ⟨some 0, 0⟩
private def memory : Mem :=
  { blocks := #[{ bytes := #[.int 0, .int 0, .int 0, .int 0], align := 4,
                   kind := .stack, live := true, addr := 4096 }] }

private def clean (s : State α) : Bool :=
  s.kernel.registration.isNone && s.kernel.mem.waiters.isEmpty && s.kernel.mem.woken.isEmpty

private def isWaiting (s : State α) : Bool :=
  match s.control with | .waiting _ => true | _ => false

private def runLoop (clock : Time.AwakeEnvironment) (deadline : Nat) (cap start : Nat) :=
  (run (input clock) 100 (fun _ => 0) (loop countdown (ts deadline) cap start)).result

/-- Run the paused loop until it first pauses (one step to decide, one to register). -/
private def paused (clock : Time.AwakeEnvironment) (deadline start : Nat)
    (wakeAt : Nat → Option (Ptr × Nat) := fun _ => none) : Outcome (Verdict Nat Nat) :=
  run (input clock wakeAt) 2 (fun _ => 0) (pausedLoop countdown (ts deadline) word 10 start) memory

private def finish (s : State (Verdict Nat Nat)) : Option (Except Error (Verdict Nat Nat)) :=
  (resume (fun _ => 0) 10 s).result

/- Clock kinds are distinct types: a wall timestamp is not a monotonic deadline, and a
monotonic duration is not a timestamp. -/
#check_failure (TimedBudget.loop countdown (⟨10⟩ : WallTimestamp) 3 0)
#check_failure (TimedBudget.loop countdown (⟨10⟩ : MonoDuration) 3 0)
#check_failure (solveWithin countdown (ts 10) 3 0)

def main : IO Unit := do
  -- Non-pausing loop: the clock ticks once per check.
  check "solved before deadline" (view (runLoop (ticking 0) 10 20 3)) "solved 42 at 3"
  check "solved one tick before the boundary" (view (runLoop (ticking 0) 4 20 3)) "solved 42 at 3"
  check "boundary now = deadline expires" (view (runLoop (ticking 0) 3 20 5)) "expired 2 at 3"
  check "deadline already reached at start" (view (runLoop (ticking 7) 3 20 5)) "expired 5 at 7"
  check "iteration cap is its own outcome" (view (runLoop (ticking 0) 50 2 5)) "capped 3"
  check "equal clock never expires; only the cap ends it"
    (view (runLoop (frozen 5 (by decide)) 10 30 100)) "capped 70"
  check "fuel exhaustion is no outcome"
    (view (run (input (ticking 0)) 2 (fun _ => 0) (loop countdown (ts 50) 20 5)).result) "pending"
  check "budget deadline is start + duration"
    (view (run (input (ticking 7)) 100 (fun _ => 0) (solveWithin countdown ⟨3⟩ 20 100)).result)
    "expired 98 at 10"
  check "budget solves within duration"
    (view (run (input (ticking 7)) 100 (fun _ => 0) (solveWithin countdown ⟨3⟩ 20 1)).result)
    "solved 42 at 9"
  check "overflowing budget is not clamped"
    (view (run (input (frozen (Time.limit - 1) (by decide))) 10 (fun _ => 0)
      (solveWithin countdown ⟨1⟩ 20 1)).result) "unrepresentable"
  check "zero budget expires at its start"
    (view (run (input (ticking 7)) 100 (fun _ => 0) (solveWithin countdown ⟨0⟩ 20 1)).result)
    "expired 1 at 8"

  -- Paused loop. Observation 0 decides, observation 1 registers the wait.
  let pending := paused (ticking 0) 10 1
  check "unsolved step pauses" (view pending.result) "pending"
  check "pause registers" (isWaiting pending.state && pending.state.kernel.registration.isSome) true

  -- Wake before timeout: the wake arrives with observation 2 < deadline 10.
  let early := paused (ticking 0) 10 1 (fun i => if i = 2 then some (word, 1) else none)
  let woken := step early.state .observe
  check "wake before timeout: wake enabled"
    (woken.state.kernel.enabled woken.state.now .wake) true
  check "wake before timeout: timeout disabled"
    (woken.state.kernel.enabled woken.state.now .timeout) false
  check "wake before timeout: early timeout rejected"
    (view (step woken.state (.normal .timeout)).result) "model error"
  let wakeReturn := step woken.state (.normal .wake)
  check "wake return cleans up" (clean wakeReturn.state) true
  check "wake before timeout: recheck solves" (view (finish wakeReturn.state)) "solved 42 at 3"

  -- Timeout: deadline 3, wait registered at observation 1.
  let timing := paused (ticking 0) 3 5
  let before := step timing.state .observe
  check "timeout not enabled before deadline"
    (before.state.kernel.enabled before.state.now .timeout) false
  let atDeadline := step before.state .observe
  check "timeout enabled at deadline observation"
    (atDeadline.state.kernel.enabled atDeadline.state.now .timeout) true
  let timedOut := step atDeadline.state (.normal .timeout)
  check "timeout return cleans up" (clean timedOut.state) true
  check "timeout reason recorded internally" timedOut.state.reasons #[.timeout]
  check "timeout: recheck expires" (view (finish timedOut.state)) "expired 4 at 4"

  -- Wake at timeout: the wake arrives with observation 3 = deadline 3.
  let race := paused (ticking 0) 3 5 (fun i => if i = 3 then some (word, 1) else none)
  let tied := step (step race.state .observe).state .observe
  check "race: wake enabled" (tied.state.kernel.enabled tied.state.now .wake) true
  check "race: timeout enabled" (tied.state.kernel.enabled tied.state.now .timeout) true
  for reason in [ReturnReason.wake, .timeout, .spurious] do
    let returned := step tied.state (.normal reason)
    check s!"race {reprStr reason}: cleanup" (clean returned.state) true
    check s!"race {reprStr reason}: same decision" (view (finish returned.state)) "expired 4 at 4"

  -- Deadline boundary at the wait itself: registration at observation 1 = deadline 1
  -- returns timeout without registering.
  let boundary := run (input (ticking 0)) 2 (fun _ => 0)
    (pausedLoop countdown (ts 1) word 10 5) memory
  check "boundary wait does not register" (clean boundary.state && !isWaiting boundary.state) true
  check "boundary wait returns by timeout" boundary.state.reasons #[.timeout]
  check "boundary wait: recheck expires" (view (finish boundary.state)) "expired 4 at 2"

  -- Spurious return before the deadline: recheck and keep solving.
  let spurious := step pending.state (.normal .spurious)
  check "spurious: recheck solves" (view (finish spurious.state)) "solved 42 at 2"

  -- No fairness: an oracle that only ever observes an equal clock never returns.
  let idle := resume (fun _ => 0) 50 (paused (frozen 5 (by decide)) 10 1).state
  check "equal clock with observe-only oracle stays pending" (view idle.result) "pending"
  check "pending wait retains registration" idle.state.kernel.registration.isSome true

  -- The paused budget path from a monotonic duration.
  let budgeted := run (input (ticking 7)) 3 (fun _ => 0)
    (within ⟨3⟩ fun d => pausedLoop countdown d word 10 5) memory
  check "paused budget registers before start + duration" budgeted.state.kernel.registration.isSome true
  let budgetedTimeout := step (step budgeted.state .observe).state (.normal .timeout)
  check "paused budget expires at start + duration" (view (finish budgetedTimeout.state))
    "expired 4 at 11"
  IO.println "C04 deadline case regressions passed"
