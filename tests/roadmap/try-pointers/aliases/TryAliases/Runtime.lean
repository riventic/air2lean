import TryAliases.Gen
import TryPointers.Gen

/-! Runtime alias and cleanup observations for pointer-form try. They mirror
`try_aliases.zig`'s native tests (the differential side) over the hand-written
`try_aliases.*` AIR and the retained compiler-exported `try_pointers.*` AIR. -/

open Zig

deriving instance DecidableEq for Except

-- Triples of error unions exceed the default instance-search size.
set_option synthInstance.maxSize 512

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

private abbrev U8 := Except ErrName (BitVec 8)

private def cell8 (v : U8) : MemM Ptr := do
  let p ← alloc .heap (Enc.size U8) 2
  store 2 p v
  pure p

private def counter (v : BitVec 32) : MemM Ptr := do
  let p ← alloc .heap 4 4
  store 4 p v
  pure p

/-- One union passed as both pointer-try operands. -/
private def samePath (v : U8) : MemM (U8 × U8) := do
  let cell ← cell8 v
  let result ← TryAliases.twoPaths cell cell 88
  pure (result, ← load U8 2 cell)

/-- Two distinct unions: the write goes to the first, the read comes from the second. -/
private def distinctPaths (a b : U8) : MemM (U8 × U8 × U8) := do
  let pa ← cell8 a
  let pb ← cell8 b
  let result ← TryAliases.twoPaths pa pb 88
  pure (result, ← load U8 2 pa, ← load U8 2 pb)

/-- A caller-held payload pointer stays live and aliases the pointer-try result. -/
private def callerAlias : MemM (Bool × BitVec 8 × U8) := do
  let cell ← cell8 (.ok 7)
  let held := errPayloadPtr (BitVec 8) cell
  match ← TryPointers.payload8 cell with
  | .error _ => pure (false, 0, .error "unexpected")
  | .ok p =>
    store 1 p (21#8)
    pure (p = held, ← load (BitVec 8) 1 held, ← load U8 2 cell)

/-- `errdefer cell.* = fallback`: the returned error is read before the cleanup store. -/
private def reset (v : U8) : MemM (Except ErrName Ptr × U8 × Bool) := do
  let cell ← cell8 v
  let result ← TryAliases.resetOnError cell 42
  pure (result, ← load U8 2 cell, result = .ok (errPayloadPtr (BitVec 8) cell))

/-- Existing `cleanup` with one counter for both cleanup pointers. -/
private def sharedCleanup (v : U8) : MemM (U8 × BitVec 32) := do
  let cell ← cell8 v
  let c ← counter 0
  let result ← TryPointers.cleanup cell c c
  pure (result, ← load (BitVec 32) 4 c)

/-- Two successive calls, as in the native test: 1 after success, 3 after error. -/
private def sharedCleanupSequence : MemM (U8 × U8 × BitVec 32) := do
  let cell ← cell8 (.ok 9)
  let c ← counter 0
  let first ← TryPointers.cleanup cell c c
  store 2 cell (.error "Bad" : U8)
  let second ← TryPointers.cleanup cell c c
  pure (first, second, ← load (BitVec 32) 4 c)

/-- An add_safe overflow in cleanup is a checked failure, not a wrapped counter. -/
private def cleanupOverflow : MemM U8 := do
  let cell ← cell8 (.error "Bad")
  let c ← counter 0xFFFFFFFF#32
  let other ← counter 0
  TryPointers.cleanup cell other c

private def writeAliasError (name : ErrName) : MemM (U8 × U8) := do
  let cell ← cell8 (.error name)
  let result ← TryPointers.writeAlias cell 88
  pure (result, ← load U8 2 cell)

private def coldSuccess : MemM (Bool × BitVec 32) := do
  let cell ← cell8 (.ok 3)
  let c ← counter 0
  let result ← TryPointers.coldPayload cell c
  pure (result = .ok (errPayloadPtr (BitVec 8) cell), ← load (BitVec 32) 4 c)

def main : IO Unit := do
  check "same union via both paths" (value (samePath (.ok 7))) (some (.ok (.ok 88, .ok 88)))
  check "same union error via both paths" (value (samePath (.error "Other")))
    (some (.ok (.error "Other", .error "Other")))
  check "distinct unions write first, read second" (value (distinctPaths (.ok 7) (.ok 9)))
    (some (.ok (.ok 9, .ok 88, .ok 9)))
  check "second path error: first union untouched" (value (distinctPaths (.ok 7) (.error "Bad")))
    (some (.ok (.error "Bad", .ok 7, .error "Bad")))
  check "first path error: second union untouched" (value (distinctPaths (.error "Other") (.ok 9)))
    (some (.ok (.error "Other", .error "Other", .ok 9)))
  check "foreign error on second path fails the finite domain"
    (value (distinctPaths (.ok 7) (.error "Foreign"))) (some (.error .unspecified))
  check "caller-held payload pointer aliases pointer-try result" (value callerAlias)
    (some (.ok (true, 21, .ok 21)))
  match value (reset (.ok 5)) with
  | some (.ok (.ok _, .ok 5, true)) => pure ()
  | other => throw (IO.userError s!"reset success: got {reprStr (other.map (·.map (·.2)))}")
  check "errdefer rewrites union after capturing the error" (value (reset (.error "Bad")))
    (some (.ok (.error "Bad", .ok 42, false)))
  check "shared counter success" (value (sharedCleanup (.ok 9))) (some (.ok (.ok 9, 1)))
  check "shared counter error: errdefer then defer" (value (sharedCleanup (.error "Bad")))
    (some (.ok (.error "Bad", 2)))
  check "shared counter native sequence" (value sharedCleanupSequence)
    (some (.ok (.ok 9, .error "Bad", 3)))
  check "cleanup add_safe overflow" (value cleanupOverflow) (some (.error .overflow))
  for name in ["Bad", "Other"] do
    check s!"writeAlias {name} leaves union unchanged" (value (writeAliasError name))
      (some (.ok (.error name, .error name)))
  check "cold payload success skips errdefer" (value coldSuccess) (some (.ok (true, 0)))
  IO.println "try pointer alias/cleanup runtime regressions passed"
