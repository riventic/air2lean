import TryPointers.Gen
import ZigLean.Sep.Try
import ZigLean.Sep.Discard

open Zig

deriving instance DecidableEq for Except

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

private def cell8 (v : Except ErrName (BitVec 8)) : MemM Ptr := do
  let p ← alloc .heap (Enc.size (Except ErrName (BitVec 8))) 2
  store 2 p v
  pure p

private def alias8 : MemM (Bool × Except ErrName (BitVec 8)) := do
  let cell ← cell8 (.ok 7)
  let result ← TryPointers.payload8 cell
  match result with
  | .error _ => pure (false, .error "unexpected")
  | .ok p =>
    store 1 p (19#8)
    pure (p = errPayloadPtr (BitVec 8) cell, ← load (Except ErrName (BitVec 8)) 2 cell)

private def alias64 : MemM (Bool × Except ErrName (BitVec 64)) := do
  let cell ← alloc .heap (Enc.size (Except ErrName (BitVec 64))) 8
  store 8 cell (Except.ok (41#64) : Except ErrName (BitVec 64))
  let result ← TryPointers.payload64 cell
  match result with
  | .error _ => pure (false, .error "unexpected")
  | .ok p =>
    store 8 p (123#64)
    pure (p = cell, ← load (Except ErrName (BitVec 64)) 8 cell)

private def aliasWrite : MemM (Except ErrName (BitVec 8) × Except ErrName (BitVec 8)) := do
  let cell ← cell8 (.ok 7)
  let result ← TryPointers.writeAlias cell 88
  pure (result, ← load (Except ErrName (BitVec 8)) 2 cell)

private def errorPreserved (name : ErrName) : MemM (Except ErrName Ptr × Except ErrName (BitVec 8)) := do
  let cell ← cell8 (.error name)
  let result ← TryPointers.payload8 cell
  pure (result, ← load (Except ErrName (BitVec 8)) 2 cell)

private def cleanupResult (v : Except ErrName (BitVec 8)) :
    MemM (Except ErrName (BitVec 8) × BitVec 32 × BitVec 32) := do
  let cell ← cell8 v
  let ordinary ← alloc .heap 4 4
  let onError ← alloc .heap 4 4
  store 4 ordinary (0#32)
  store 4 onError (0#32)
  let result ← TryPointers.cleanup cell ordinary onError
  pure (result, ← load (BitVec 32) 4 ordinary, ← load (BitVec 32) 4 onError)

private def coldResult : MemM (Except ErrName Ptr × BitVec 32) := do
  let cell ← cell8 (.error "Bad")
  let onError ← alloc .heap 4 4
  store 4 onError (0#32)
  let result ← TryPointers.coldPayload cell onError
  pure (result, ← load (BitVec 32) 4 onError)

-- The payload has no initialized bytes: the whole unused read may not decode it.
private def undefinedPayload : MemM (Except ErrName (BitVec 8)) := do
  let cell ← alloc .heap (Enc.size (Except ErrName (BitVec 8))) 2
  let _ ← errSetOk (BitVec 8) 2 cell
  match ← TryPointers.payload8 cell with
  | .error e => pure (.error e)
  | .ok p =>
    store 1 p (99#8)
    load (Except ErrName (BitVec 8)) 2 cell

-- The tag exists, but the full error-union object does not. Its unused read must fail.
private def truncatedObject : MemM (Except ErrName Ptr) := do
  let cell ← alloc .heap 2 2
  storeBytes cell 2 (errBytes none)
  TryPointers.payload8 cell

-- The tag's two-byte alignment is satisfied; the original whole load's eight-byte
-- alignment is not. Discarding its result must preserve that stronger access check.
private def wholeObjectAlignment : MemM (Except ErrName Ptr) := do
  let base ← alloc .heap 18 8
  let cell := base.add 2
  storeBytes (cell.add 8) 1 (errBytes none)
  TryPointers.payload64 cell

private def readFootprints : MemM (Array Nat) := do
  let cell ← cell8 (.ok 7)
  let before := (← get).footprint.size
  let _ ← TryPointers.payload8 cell
  let m ← get
  pure ((m.footprint.extract before m.footprint.size).map (·.len))

private def discardedUndefined : MemM (Array Nat) := do
  let p ← alloc .heap 4 4
  loadDiscardBytes 4 4 p
  pure ((← get).footprint.map (·.len))

private def discardedRace : MemM Unit := do
  let p ← alloc .heap 4 4
  let prior : FootprintEntry := {
    tid := 0
    clock := #[1, 0]
    block := p.block.getD 0
    off := 0
    len := 4
    kind := .write }
  modify fun m => { m with
    current := 1
    clocks := #[#[1, 0], #[0, 0]]
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }]
    footprint := #[prior] }
  loadDiscardBytes 4 4 p

def main : IO Unit := do
  check "u8 original address and aliased write" (value alias8) (some (.ok (true, .ok 19)))
  check "u64 payload-first layout preserves address" (value alias64) (some (.ok (true, .ok 123)))
  check "two pointer-try results alias" (value aliasWrite) (some (.ok (.ok 88, .ok 88)))
  for name in ["Bad", "Other"] do
    check s!"propagate {name} and preserve union" (value (errorPreserved name))
      (some (.ok (.error name, .error name)))
  check "success runs defer only" (value (cleanupResult (.ok 9))) (some (.ok (.ok 9, 1, 0)))
  check "error runs defer and errdefer" (value (cleanupResult (.error "Bad")))
    (some (.ok (.error "Bad", 1, 1)))
  check "cold error body" (value coldResult) (some (.ok (.error "Bad", 1)))
  check "pointer try does not decode undefined payload" (value undefinedPayload) (some (.ok (.ok 99)))
  check "invalid provenance still rejects" (value (tryPayloadPtr (BitVec 8) 2 default))
    (some (.error .illegal))
  check "unused whole-object load retains bounds" (value truncatedObject) (some (.error .illegal))
  check "unused whole-object load retains alignment" (value wholeObjectAlignment) (some (.error .illegal))
  check "whole read and tag read retain both footprints" (value readFootprints) (some (.ok #[4, 2]))
  check "discarded undefined bytes still record full read" (value discardedUndefined) (some (.ok #[4]))
  check "discarded read still rejects races" (value discardedRace) (some (.error .illegal))
  IO.println "try pointer source-generated runtime regressions passed"
