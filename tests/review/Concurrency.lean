import ZigLean.Conc

open Zig

deriving instance DecidableEq for Except

namespace ConcurrencyRegression

/-- A spawn that this test expects to succeed (an `available` environment). -/
private def spawnT {T : Type} (t : T) : ConcM T ThreadId := do
  match ← ConcM.sync (.spawn t) with
  | .ok tid => pure tid
  | .error _ => throw .panic

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def value {α : Type} (r : Sched.Out α) : Option (Except Error α) :=
  r.map (·.map Prod.fst)

private def select (pick diverge : Bool) : ConcM Unit Nat := do
  let c : Nat ← if pick then ConcM.sync (.pick fun _ => 2) else ConcM.sync (.choose 2)
  if c = 0 then
    if diverge then fun _ _ => .leaf none else throw .panic
  else pure 7

private def childMain : ConcM Unit Nat := do
  let tid ← spawnT ()
  let _ ← ConcM.sync (.join tid)
  pure 7

/-- The schedule search used by the differential harness, bounded to these small trees. -/
private partial def search (run : (Nat → Nat) → Sched.Out Nat × Array Nat)
    (target : Option (Except Error Nat)) : Option (Except Error Nat) :=
  let rec go (pre : Array Nat) (runs : Nat) (first : Option (Option (Except Error Nat))) :=
    let (r, opts) := run fun i => pre.getD i 0
    let line := value r
    if line = target then line else
    let first := first.orElse fun _ => some line
    let rec next (i : Nat) : Option (Array Nat) :=
      if i = 0 then none else
      let j := i - 1
      let c := pre.getD j 0
      if c + 1 < opts[j]! then
        some (((Array.range j).map fun x => pre.getD x 0).push (c + 1))
      else next j
    match next opts.size with
    | some p => if runs ≥ 100 then first.getD line else go p (runs + 1) first
    | none => first.getD line
  go #[] 0 none

private def traceTests : IO Unit := do
  for pick in [false, true] do
    for diverge in [false, true] do
      let label := s!"pick={pick}, diverge={diverge}"
      let run := fun o => Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) 20 o (select pick diverge) {}
      let (r, trace) := run fun _ => 0
      check ("main trace " ++ label) trace #[1, 2]
      check ("main failure " ++ label) (value r)
        (if diverge then none else some (.error .panic))
      check ("main search " ++ label) (search run (some (.ok 7))) (some (.ok 7))
      let runChild := fun o => Sched.runTrace ⟨.any, .available⟩ (fun _ => select pick diverge *> pure ())
        20 o childMain {}
      let (r, trace) := runChild fun _ => 0
      check ("child trace " ++ label) trace #[1, 1, 1, 2]
      check ("child failure " ++ label) (value r)
        (if diverge then none else some (.error .panic))
      check ("child search " ++ label) (search runChild (some (.ok 7))) (some (.ok 7))

private def catches (op : SyncOp Unit) : ConcM Unit Nat :=
  tryCatch (do let _ ← ConcM.sync op; throw .illegal) (fun _ => pure 7)

private def catchTests : IO Unit := do
  let run := fun (fuel : Nat) (x : ConcM Unit Nat) =>
    value (Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) fuel (fun _ => 0) x {}).1
  check "immediate catch" (run 10 (tryCatch (throw .panic) (fun _ => pure 7))) (some (.ok 7))
  for op in [SyncOp.yield, .choose 2, .pick fun _ => 2] do
    check "catch after sync" (run 10 (catches op)) (some (.ok 7))
  let multiple : ConcM Unit Nat := tryCatch
    (do let _ ← ConcM.sync .yield; let _ ← ConcM.sync (.choose 2); throw .panic)
    (fun _ => do let _ ← ConcM.sync .yield; pure 7)
  check "multiple syncs and handler sync" (run 10 multiple) (some (.ok 7))
  let handlerSync : ConcM Unit Nat := tryCatch
    (do let _ ← ConcM.sync .yield; throw .panic)
    (fun _ => do let _ ← ConcM.sync .yield; pure 7)
  check "handler consumes remaining depth" (run 1 handlerSync) none
  check "handler has sufficient remaining depth" (run 2 handlerSync) (some (.ok 7))
  let nested : ConcM Unit Nat := tryCatch
    (tryCatch (do let _ ← ConcM.sync .yield; throw .panic)
      (fun _ => do let _ ← ConcM.sync .yield; throw .illegal))
    (fun _ => pure 7)
  check "nested catches" (run 10 nested) (some (.ok 7))
  let joined : ConcM Unit Nat := tryCatch
    (do let tid ← spawnT ()
        let _ ← ConcM.sync (.join tid)
        throw .panic)
    (fun _ => pure 7)
  check "catch after successful spawn and join" (run 20 joined) (some (.ok 7))
  let waited : ConcM Unit Nat := tryCatch
    (do let p ← ConcM.liftMem (alloc .heap 4 4)
        ConcM.liftMem (store 4 p (1#32))
        let _ ← ConcM.sync (.wait p 0)
        throw .panic)
    (fun _ => pure 7)
  check "catch after successful futex wait" (run 10 waited) (some (.ok 7))
  let rollback : ConcM Unit Nat := tryCatch
    (do ConcM.liftMem (modify fun m => { m with allocs := 99 }); throw .panic)
    (fun _ => ConcM.liftMem (do pure (← get).allocs))
  check "immediate segment state recovery" (run 10 rollback) (some (.ok 0))
  let shared : ConcM Unit Nat := do
    let tid ← spawnT ()
    let v ← tryCatch
      (do let _ ← ConcM.sync .yield
          ConcM.liftMem (modify fun m => { m with allocs := 99 })
          throw .panic)
      (fun _ => ConcM.liftMem (do pure (← get).allocs))
    let _ ← ConcM.sync (.join tid)
    pure v
  let dispatch : Unit → ConcM Unit Unit := fun _ =>
    ConcM.liftMem (modify fun m => { m with allocs := 42 })
  check "catch keeps another thread changes"
    (value (Sched.runTrace ⟨.any, .available⟩ dispatch 10 (fun i => if i = 1 then 1 else 0) shared {}).1)
    (some (.ok 42))
  -- Scheduler-origin failures occur before the successful sync continuation;
  -- the structural catch handles thread errors but cannot intercept these.
  check "scheduler invalid join is fatal"
    (run 10 (tryCatch (do let _ ← ConcM.sync (.join 99); pure 0) (fun _ => pure 7)))
    (some (.error .illegal))
  check "scheduler invalid wait is fatal"
    (run 10 (tryCatch (do let _ ← ConcM.sync (.wait ⟨none, 0⟩ 0); pure 0) (fun _ => pure 7)))
    (some (.error .illegal))

private def joinTests : IO Unit := do
  let run := fun (x : ConcM Unit Unit) =>
    value (Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) 20 (fun _ => 0) x {}).1
  for tid in [0, 99] do
    check "invalid join" (run (ConcM.sync (.join tid))) (some (.error .illegal))
  let repeated : ConcM Unit Unit := do
    let tid ← spawnT ()
    let _ ← ConcM.sync (.join tid)
    ConcM.sync (.join tid)
  check "repeated join" (run repeated) (some (.error .illegal))
  let wrongOwner : ConcM Nat Unit := do
    let _ ← spawnT 2
    let _ ← spawnT 0
    ConcM.sync (.join 1)
  let dispatch : Nat → ConcM Nat Unit := fun tid =>
    if tid = 0 then pure () else ConcM.sync (.join tid)
  check "wrong owner of live child"
    (value (Sched.runTrace ⟨.any, .available⟩ dispatch 20 (fun _ => 0) wrongOwner {}).1)
    (some (.error .illegal))
  let valid : ConcM Unit Unit := do
    let tid ← spawnT ()
    ConcM.sync (.join tid)
  let (r, trace) := Sched.runTrace ⟨.any, .available⟩ (fun _ => do let _ ← ConcM.sync .yield; pure ())
    20 (fun _ => 0) valid {}
  check "valid live child join" (value r) (some (.ok ()))
  check "valid join waits for child" trace #[1, 1, 1, 1]
  match r with
  | some (.ok (_, m)) =>
    check "joined child clock merged" (VClock.le m.clocks[1]! m.clocks[0]!) true
    check "child marked joined" (m.threads[1]!).joined true
  | _ => throw (IO.userError "valid join had no memory result")

/-- Audit #6: a futex wake wakes the waiters that the oracle picks, not the earliest ones. -/
private def wakeTests : IO Unit := do
  let p : Ptr := ⟨some 0, 0⟩
  let m : Mem := { waiters := #[(1, p), (2, p), (3, ⟨some 1, 0⟩)] }
  let woken := fun (n : Nat) (cs : List Nat) =>
    (((Thread.futexWake p n cs).run m).run).map fun r => r.map fun (_, m') => (m'.woken, m'.waiters)
  check "wake picks the first waiter" (woken 1 [0]) (some (.ok (#[1], #[(2, p), (3, ⟨some 1, 0⟩)])))
  check "wake picks a later waiter" (woken 1 [1]) (some (.ok (#[2], #[(1, p), (3, ⟨some 1, 0⟩)])))
  check "wake of two in either order" (woken 2 [1, 0]) (some (.ok (#[2, 1], #[(3, ⟨some 1, 0⟩)])))
  check "a wake never wakes a waiter at another futex" (woken 5 [2, 2, 2])
    (some (.ok (#[1, 2], #[(3, ⟨some 1, 0⟩)])))
  -- The scheduler asks the oracle for one choice per woken waiter: 2 options, then 1.
  let s : Sched.State Unit Unit := { main := .done, kids := #[], mem := m, step := 0, trace := #[] }
  check "wake choices" ((s.chooseWake (fun _ => 1) p 2).1, (s.chooseWake (fun _ => 1) p 2).2.trace)
    ([1, 0], #[2, 1])

/-- Audit #14: the kernel's compare of a futex wait is an atomic read of the word, so a plain
write that races with it is `.illegal`; after the join it is ordered. -/
private def futexReadTests : IO Unit := do
  let dispatch : Ptr → ConcM Ptr Unit := fun p => ConcM.liftMem (store 4 p (1#32))
  let prog (joinFirst : Bool) : ConcM Ptr Nat := do
    let p ← ConcM.liftMem (alloc .heap 4 4)
    ConcM.liftMem (store 4 p (0#32))
    let tid ← spawnT p
    if joinFirst then ConcM.sync (.join tid)
    let _ ← ConcM.sync (.wait p 5)
    unless joinFirst do ConcM.sync (.join tid)
    pure 7
  let run := fun (o : Nat) (joinFirst : Bool) =>
    value (Sched.runTrace ⟨.any, .available⟩ dispatch 40 (fun _ => o) (prog joinFirst) {}).1
  for o in [0, 1] do
    check s!"futex compare races with a plain write (oracle {o})" (run o false)
      (some (.error .illegal))
  check "futex compare after the join" (run 0 true) (some (.ok 7))

end ConcurrencyRegression

def main : IO Unit := do
  ConcurrencyRegression.wakeTests
  ConcurrencyRegression.futexReadTests
  ConcurrencyRegression.traceTests
  ConcurrencyRegression.catchTests
  ConcurrencyRegression.joinTests
  IO.println "Concurrency regressions passed"
