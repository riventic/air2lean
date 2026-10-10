import TryPointers.Gen
import ZigLean.Sep.Try
import ZigLean.Sep.Discard
import ZigLean.Mem.ErrWidth

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

-- The payload pointer is formed like every derived pointer (`ptrProject`, MM-3).
private def payloadFormed : MemM Bool := do
  let cell ← cell8 (.ok 7)
  let tried ← tryPayloadPtr (BitVec 8) 2 cell
  let set ← errSetOk (BitVec 8) 2 cell
  pure (tried == .ok (cell.add 2) && set == cell.add 2)

-- A `u16` reached through a cast to `*anyerror!u8`: the code fits, the payload pointer is
-- one past the end (defined, as `getelementptr inbounds`), and the payload access is illegal.
private def castCell16 : MemM Ptr := do
  let cell ← alloc .heap 2 2
  store 2 cell (0#16)
  pure cell

private def truncatedCast8Formed : MemM Bool := do
  let cell ← castCell16
  pure ((← tryPayloadPtr (BitVec 8) 2 cell) == .ok (cell.add 2))

private def truncatedCast8 : MemM (BitVec 8) := do
  let cell ← castCell16
  match ← tryPayloadPtr (BitVec 8) 2 cell with
  | .error _ => pure 0#8
  | .ok q => load (BitVec 8) 1 q

-- A `u64` reached through a cast to `*anyerror!u64`: the code after the payload is missing.
private def truncatedCast64 : MemM (Except ErrName Ptr) := do
  let cell ← alloc .heap 8 8
  store 8 cell (0#64)
  tryPayloadPtr (BitVec 64) 8 cell

private def truncatedSet8 : MemM Ptr := do
  let cell ← alloc .heap 1 2
  errSetOk (BitVec 8) 2 cell

-- A layout where only the formation check rejects: a 24-bit error code (4 bytes) and a
-- synthetic payload alignment 3 put the payload at offset 6, past a 4-byte object that holds
-- just the code. The code access succeeds; forming the payload pointer is illegal.
private structure Align3

private instance : Enc Align3 where
  size := 1
  align := 3
  encode _ := #[.undef]
  decode _ := pure ⟨⟩

private def truncatedWideTry : MemM (Except ErrName Ptr) := do
  let cell ← alloc .heap 4 4
  storeBytes cell 4 (errBytesW 24 none)
  tryPayloadPtrW 24 Align3 4 cell

-- The same layout in an object large enough for the payload: formed.
private def wideAlign3Formed : MemM Bool := do
  let cell ← alloc .heap 8 4
  storeBytes cell 4 (errBytesW 24 none)
  pure ((← tryPayloadPtrW 24 Align3 4 cell) == .ok (cell.add 6))

private def truncatedWideSet : MemM Ptr := do
  let cell ← alloc .heap 4 4
  errSetOkW 24 Align3 4 cell

private def wideFormed : MemM Bool := do
  let cell ← alloc .heap 8 4
  let set ← errSetOkW 24 (BitVec 8) 4 cell
  let tried ← tryPayloadPtrW 24 (BitVec 8) 4 cell
  pure (tried == .ok (cell.add 4) && set == cell.add 4)

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

-- Compare the complete observable Result and memory representation, including every
-- clock and footprint field. The universal loadDiscardBytes_eq lemma covers all states.
private def discardMatchesRaw (n a : Nat) (p : Ptr) (m : Mem) : Bool :=
  reprStr ((loadDiscardBytes n a p).run m).run ==
    reprStr (((do let _ ← loadBytes p n a; pure ()) : MemM Unit).run m).run

private def racedReadState (p : Ptr) (m : Mem) : Mem :=
  let prior : FootprintEntry := {
    tid := 0
    clock := #[1, 0]
    block := p.block.getD 0
    off := 0
    len := 4
    kind := .write }
  { m with
    current := 1
    clocks := #[#[1, 0], #[0, 0]]
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }]
    footprint := #[prior] }

private def discardedEquivalent : MemM Bool := do
  let p ← alloc .heap 4 4
  let m ← get
  let raced := racedReadState p m
  pure (discardMatchesRaw 4 4 p m && discardMatchesRaw 4 4 p raced &&
    discardMatchesRaw 4 4 (p.add 1) m && discardMatchesRaw 5 4 p m &&
    discardMatchesRaw 4 4 default m && discardMatchesRaw 4 4 (p.add 1) raced)

private def discardedRace : MemM Unit := do
  let p ← alloc .heap 4 4
  modify (racedReadState p)
  loadDiscardBytes 4 4 p

def main : IO Unit := do
  check "u8 original address and aliased write" (value alias8) (some (.ok (true, .ok 19)))
  check "u64 payload-first layout preserves address" (value alias64) (some (.ok (true, .ok 123)))
  check "two pointer-try results alias" (value aliasWrite) (some (.ok (.ok 88, .ok 88)))
  for name in ["Bad", "Other"] do
    check s!"propagate {name} and preserve union" (value (errorPreserved name))
      (some (.ok (.error name, .error name)))
  check "foreign error name fails the finite source domain" (value (errorPreserved "Foreign"))
    (some (.error .unspecified))
  check "success runs defer only" (value (cleanupResult (.ok 9))) (some (.ok (.ok 9, 1, 0)))
  check "error runs defer and errdefer" (value (cleanupResult (.error "Bad")))
    (some (.ok (.error "Bad", 1, 1)))
  check "cold error body" (value coldResult) (some (.ok (.error "Bad", 1)))
  check "pointer try does not decode undefined payload" (value undefinedPayload) (some (.ok (.ok 99)))
  check "invalid provenance still rejects" (value (tryPayloadPtr (BitVec 8) 2 default))
    (some (.error .illegal))
  check "unused whole-object load retains bounds" (value truncatedObject) (some (.error .illegal))
  check "unused whole-object load retains alignment" (value wholeObjectAlignment) (some (.error .illegal))
  check "pointer try and payload set form the payload pointer" (value payloadFormed)
    (some (.ok true))
  check "truncated object through a cast: payload pointer one past the end"
    (value truncatedCast8Formed) (some (.ok true))
  check "truncated object through a cast: payload access illegal" (value truncatedCast8)
    (some (.error .illegal))
  check "truncated payload-first object through a cast: code access illegal"
    (value truncatedCast64) (some (.error .illegal))
  check "truncated object through a cast: payload set illegal" (value truncatedSet8)
    (some (.error .illegal))
  check "payload pointer past a truncated object: try illegal" (value truncatedWideTry)
    (some (.error .illegal))
  check "payload pointer past a truncated object: set illegal" (value truncatedWideSet)
    (some (.error .illegal))
  check "payload pointer inside the object: try formed" (value wideAlign3Formed) (some (.ok true))
  check "24-bit code: pointer try and payload set form the payload pointer" (value wideFormed)
    (some (.ok true))
  check "whole read and tag read retain both footprints" (value readFootprints) (some (.ok #[4, 2]))
  check "discarded undefined bytes still record full read" (value discardedUndefined) (some (.ok #[4]))
  check "discarded read still rejects races" (value discardedRace) (some (.error .illegal))
  check "direct discarded access equals raw read for successes and errors"
    (value discardedEquivalent) (some (.ok true))
  IO.println "try pointer source-generated runtime regressions passed"
