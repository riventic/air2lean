import ZigLean
import ZigLean.Conc.WeakCas

open Zig

deriving instance DecidableEq for Except

private def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

private def equal [DecidableEq α] (actual expected : α) : Bool := decide (actual = expected)

private def assertC11 (ok : Bool) (message : String) : IO Unit :=
  unless ok do
    IO.eprintln s!"C11_ASSERTION: {message}"
    IO.Process.exit 85

private def summary (weak : Bool) (choice : Nat) (expected : BitVec 8) : MemM
    (Option (BitVec 8) × Nat × Nat × Nat × Nat × BitVec 8) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let before ← get
  let count := if weak then weakCasCount 8 .acqRel 1 p expected before
    else casCount 8 .acqRel 1 p expected before
  let r ← if weak then cmpxchgWeakAt choice .acqRel .acquire 1 p expected (7#8)
    else cmpxchgAt choice .acqRel .acquire 1 p expected (7#8)
  let m ← get
  let written := (m.footprint.filter fun a => a.kind == .atomicWrite).size
  let stored ← load (BitVec 8) 1 p
  pure (r, count, written, m.atomics[0]!.msgs.size, m.clocks[0]!.get 0, stored)

-- Observe every result field explicitly, avoiding nested product equality instances.
private def summaryMatches
    (x : MemM (Option (BitVec 8) × Nat × Nat × Nat × Nat × BitVec 8))
    (result : Option (BitVec 8)) (choices writes messages clock : Nat) (stored : BitVec 8) : Bool :=
  match value x with
  | some (.ok (r, c, w, ms, cl, v)) =>
    r == result && c == choices && w == writes && ms == messages && cl == clock && v == stored
  | _ => false

-- Kernel reduction checks source-result branches and memory events, not compiler execution.
example : summaryMatches (summary true 1 (42#8)) (some 42#8) 2 0 1 2 (42#8) = true := by decide +kernel
example : summaryMatches (summary true 0 (42#8)) none 2 1 2 3 (7#8) = true := by decide +kernel
example : summaryMatches (summary false 0 (42#8)) none 1 1 2 3 (7#8) = true := by decide +kernel
example : summaryMatches (summary true 0 (99#8)) (some 42#8) 1 0 1 2 (42#8) = true := by decide +kernel

private def failureAcquire (fail : AtomicOrder) : MemM (Option (BitVec 8) × Nat × Nat) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let child ← Thread.fork
  modify fun m => { m with current := child }
  atomicStoreAt 0 .release 1 p (42#8)
  modify fun m => { m with current := 0 }
  let r ← cmpxchgWeakAt 2 .acqRel fail 1 p (42#8) (7#8)
  let m ← get
  pure (r, m.clocks[0]!.get child, m.atomics[0]!.msgs.size)

private def predecessor : MemM (Option (BitVec 8) × Nat × Nat × Nat) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let child ← Thread.fork
  modify fun m => { m with current := child }
  let _ ← cmpxchgAt 0 .relaxed .relaxed 1 p (42#8) (7#8)
  modify fun m => { m with current := 0 }
  let m ← get
  let weakCount := weakCasCount 8 .relaxed 1 p (42#8) m
  let strongCount := casCount 8 .relaxed 1 p (42#8) m
  let r ← cmpxchgWeakAt 1 .relaxed .relaxed 1 p (42#8) (9#8)
  pure (r, weakCount, strongCount, (← get).atomics[0]!.msgs.size)

private def packedFailure : MemM (Option Bool × Bool × Nat) := do
  let p ← alloc .heap 1 1
  store 1 p false
  let r ← cmpxchgWeakAs 1 .relaxed .relaxed 1 p false true
  let v ← load Bool 1 p
  pure (r, v, (← get).atomics[0]!.msgs.size)

private def withPlain (readFirst plainWrite succeeds : Bool) : MemM (Option (BitVec 8)) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let child ← Thread.fork
  let plain : MemM Unit := if plainWrite then store 1 p (42#8)
    else do let _ ← load (BitVec 8) 1 p; pure ()
  if readFirst then plain
  modify fun m => { m with current := child }
  let r ← cmpxchgWeakAt (if succeeds then 0 else 1) .relaxed .relaxed 1 p (42#8) (7#8)
  modify fun m => { m with current := 0 }
  if !readFirst then plain
  pure r

-- Structural recursion exposes each actual memory transition to kernel reduction.
-- None and errors propagate, success stops, and any failed read consumes one attempt.
private def retryRun (p : Ptr) : List Nat → Mem → Option (Except Error (Bool × Mem))
  | [], m => some (.ok (false, m))
  | c :: cs, m =>
    match ((cmpxchgWeakAt c .acqRel .acquire 1 p (42#8) (7#8)).run m).run with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (none, m')) => some (.ok (true, m'))
    | some (.ok (some _, m')) => retryRun p cs m'

private def retry (p : Ptr) (choices : List Nat) : MemM Bool :=
  fun m => ExceptT.mk (retryRun p choices m)

private def retrySummary (choices : List Nat) : MemM (Bool × BitVec 8 × Nat) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let done ← retry p choices
  let v ← load (BitVec 8) 1 p
  pure (done, v, (← get).atomics[0]!.msgs.size)

private def retrySafe (cs : List Nat) : Bool :=
  match value (retrySummary cs) with
  | some (.ok (true, v, count)) => v == 7#8 && count == 2
  | some (.ok (false, v, count)) => v == 42#8 && count == 1
  | _ => false

-- Every sequence of weak success/failure choices for this bounded three-attempt source client.
example : ([0, 1].all fun a => [0, 1].all fun b => [0, 1].all fun c =>
    retrySafe [a, b, c]) = true := by decide +kernel

private def retryBody : CM Unit Unit (Option (BitVec 8)) :=
  cmpxchgWeakC .acqRel .acquire 1 ({ block := some 0, off := 0 } : Ptr) (42#8) (7#8)

-- Generic arbitrary-choice retry safety: the transition obligations include spurious failure.
example {P : Conc.Proto Unit Unit}
    (inv : Unit → (ThreadId → Unit) → Mem → Nat → Prop)
    (post : Option (BitVec 8) × Unit → (ThreadId → Unit) → Mem → Nat → Prop)
    (step : ∀ s G m n, inv s G m n → P.WP 0 (retryBody.run s)
      (fun r G' m' d => if r.1.isSome then inv r.2 G' m' d ∧ d < n
        else post r G' m' d) G m n) :
    ∀ s G m n, inv s G m n → P.WP 0
      ((Zig.loop retryBody Option.isSome).run s) post G m n :=
  Conc.Proto.WP.weakCasRetry inv post step

def main : IO Unit := do
  assertC11 (summaryMatches (summary true 1 (42#8)) (some 42#8) 2 0 1 2 (42#8))
    "matching weak failure is read only"
  assertC11 (summaryMatches (summary true 0 (42#8)) none 2 1 2 3 (7#8))
    "weak success remains an RMW"
  assertC11 (summaryMatches (summary false 0 (42#8)) none 1 1 2 3 (7#8))
    "strong matching CAS has no spurious choice"
  assertC11 (summaryMatches (summary true 0 (99#8)) (some 42#8) 1 0 1 2 (42#8))
    "mismatching weak CAS remains a failed read"
  assertC11 (equal (value packedFailure) (some (.ok (some false, false, 1))))
    "Packed weak failure preserves its value"
  assertC11 (equal (value predecessor) (some (.ok (some 42#8, 2, 1, 2))))
    "failed weak read can observe an RMW predecessor"
  let relaxed := value (failureAcquire .relaxed)
  let acquired := value (failureAcquire .acquire)
  assertC11 (match relaxed, acquired with
    | some (.ok (some r, 0, 2)), some (.ok (some a, cl, 2)) => r == 42#8 && a == 42#8 && cl > 0
    | _, _ => false) "spurious failure applies only its failure-order acquire"
  assertC11 ([0, 1].all fun a => [0, 1].all fun b => [0, 1].all fun c => retrySafe [a, b, c])
    "bounded retry is safe for all permitted choices"
  for first in [false, true] do
    assertC11 (equal (value (withPlain first false false)) (some (.ok (some 42#8))))
      "matching weak failure and concurrent plain read commute"
    assertC11 (equal (value (withPlain first true false)) (some (.error .illegal)))
      "matching weak failure still races with a plain write"
    assertC11 (equal (value (withPlain first false true)) (some (.error .illegal)))
      "successful weak CAS still races with a plain read"
  IO.println "Weak CAS runtime regressions passed"
