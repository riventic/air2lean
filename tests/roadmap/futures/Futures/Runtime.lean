import Futures.Gen

/-! C08 runtime evidence for the generated `Io.Future` code: every schedule of each fixture,
enumerated by a depth-first search of the scheduler's choice tree (`Sched.runTrace`). These are
checks of the executable model, not proofs; `Futures/Proofs.lean` holds the kernel proofs. -/

open Zig

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Every result of `main` over all schedules (each choice of each turn), at most `cap` runs. -/
partial def allOutcomes {Tgt α : Type} (dispatch : Tgt → ConcM Tgt Unit) (fuel cap : Nat)
    (main : ConcM Tgt α) (m0 : Mem) : Array (Option (Except Error α)) := Id.run do
  let mut out := #[]
  let mut todo : List (Array Nat) := [#[]]
  while !todo.isEmpty && out.size < cap do
    let pre := todo.head!
    todo := todo.tail!
    let (r, opts) := Sched.runTrace ⟨.any, .available⟩ dispatch fuel (fun i => pre.getD i 0) main m0
    out := out.push (r.map (·.map (·.1)))
    -- Branch on every later choice that this run took as 0.
    for i in [pre.size:opts.size] do
      for c in [1:opts[i]!] do
        todo := (pre ++ Array.replicate (i - pre.size) 0 |>.push c) :: todo
  return out

private def bv (n : Nat) : BitVec 32 := BitVec.ofNat 32 n

private def outcomes {α : Type} (x : ConcM Futures.Tgt α) : Array (Option (Except Error α)) :=
  allOutcomes Futures.dispatch 200 5000 x (Futures.mem0 .fresh)

private def onlyOk {α : Type} [BEq α] (rs : Array (Option (Except Error α))) (v : α) : Bool :=
  !rs.isEmpty && rs.all fun r => match r with
    | some (.ok a) => a == v
    | _ => false

private def isIllegal {α : Type} : Option (Except Error α) → Bool
  | some (.error .illegal) => true
  | _ => false

/-- Hand-written targets for the negative checks: a squaring task and a thread that awaits a
future it did not create. -/
inductive H where
  | square (slot : Ptr) (x : BitVec 32)
  | awaiter (p : Ptr)

def hDispatch : H → ConcM H Unit
  | .square slot x => ConcM.liftMem (Future.complete slot (x * x))
  | .awaiter p => discard ((awaitC (α := BitVec 32) ⟨⟩ p : CM H Unit (BitVec 32)).run' ())

/-- The main thread creates a future; a second thread awaits it (only the spawner may). -/
def foreignAwait : ConcM H Unit := (do
  let f ← asyncC (α := BitVec 32) (fun slot => H.square slot 3) (pure (3 * 3))
  let p ← callMC (alloc .stack 16 8)
  callMC (store 8 p f)
  let helper := (← spawnC (H.awaiter p)).toOption.getD 0
  joinC helper
  let _ ← awaitC (α := BitVec 32) ⟨⟩ p
  pure () : CM H Unit Unit).run' ()

/-- Two threads consume one future concurrently (`await` is not threadsafe). -/
def doubleAwait : ConcM H (BitVec 32) := (do
  let f ← asyncC (α := BitVec 32) (fun slot => H.square slot 3) (pure (3 * 3))
  let p ← callMC (alloc .stack 16 8)
  callMC (store 8 p f)
  let helper := (← spawnC (H.awaiter p)).toOption.getD 0
  let r ← awaitC (α := BitVec 32) ⟨⟩ p
  joinC helper
  pure r : CM H Unit (BitVec 32)).run' ()

/-- `Io.async` without `await`/`cancel`: the task is never consumed. -/
def leak : ConcM H Unit := (do
  let _ ← asyncC (α := BitVec 32) (fun slot => H.square slot 3) (pure (3 * 3))
  pure () : CM H Unit Unit).run' ()

def main : IO Unit := do
  for x in [0, 1, 7, 65536, 4294967295] do
    require (onlyOk (outcomes (Futures.awaitValue ⟨⟩ (bv x))) (bv x * bv x))
      s!"await did not return the task result for {x}"
    require (onlyOk (outcomes (Futures.awaitTwice ⟨⟩ (bv x))) (bv x * bv x + bv x * bv x))
      s!"a second await did not return the stored result for {x}"
    require (onlyOk (outcomes (Futures.awaitOwned ⟨⟩ (bv x))) (bv x))
      s!"the task's write through its captured pointer was lost for {x}"
    let canceled := outcomes (Futures.cancelValue ⟨⟩ (bv x))
    require (canceled.all fun r => match r with
        | some (.ok (.ok v)) => v == bv x + 1
        | some (.ok (.error e)) => e == "Canceled"
        | _ => false) s!"cancel gave an outcome other than the result or Canceled for {x}"
    require (canceled.any (· matches some (.ok (.error _)))) s!"no schedule observed Canceled for {x}"
    require (canceled.any (· matches some (.ok (.ok _)))) s!"no schedule completed before cancel for {x}"
  require (onlyOk (outcomes (Futures.awaitError ⟨⟩ 0)) (.error "Zero")) "error not propagated"
  require (onlyOk (outcomes (Futures.awaitError ⟨⟩ 5)) (.ok 4)) "error-union payload not returned"
  let leaked := allOutcomes hDispatch 200 5000 leak {}
  require (!leaked.isEmpty && leaked.all isIllegal) "an unconsumed future was not reported"
  let foreign := allOutcomes hDispatch 200 5000 foreignAwait {}
  require (!foreign.isEmpty && foreign.all isIllegal) "a future was consumed by another thread"
  let double := allOutcomes hDispatch 200 5000 doubleAwait {}
  require (!double.isEmpty && double.all isIllegal) "two concurrent awaits were not reported"
  IO.println s!"futures runtime schedules passed ({(outcomes (Futures.cancelValue ⟨⟩ 1)).size} cancel, \
    {double.size} double-await, {foreign.size} foreign-await schedules)"
