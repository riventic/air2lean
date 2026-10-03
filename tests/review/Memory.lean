import ZigLean.Mem

open Zig

deriving instance DecidableEq for Except

namespace MemoryRegression

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def value (x : MemM α) : Option (Except Error α) :=
  (x.run {}).run.map (·.map Prod.fst)

-- Decoding a zero-sized type still matters: use an encoding whose value is not its default.
private structure EmptyValue where
  tag : Nat := 0
  deriving DecidableEq, Repr

private instance : Enc EmptyValue where
  size := 0
  align := 1
  encode _ := #[]
  decode bs := if bs.isEmpty then pure ⟨17⟩ else throw .illegal

private structure RejectedEmpty where
  deriving Repr

private instance : Enc RejectedEmpty where
  size := 0
  align := 1
  encode _ := #[]
  decode _ := throw .unspecified

private def zeroTests : IO Unit := do
  let p := zeroAllocPtr 1
  check "zero-sized memset with positive count"
    (value (memset (α := Unit) 1 p 5 (some ()))) (some (.ok ()))
  check "zero-sized undefined memset"
    (value (memset (α := Unit) 1 p 5 none)) (some (.ok ()))
  check "zero-sized memmove with positive count"
    (value (memmove 0 1 1 p p 5)) (some (.ok ()))
  check "empty nonzero-size memmove"
    (value (memmove 8 8 8 p p 0)) (some (.ok ()))
  check "zero-sized slice preserves item count and decoding"
    (value (readSlice EmptyValue 1 ⟨p, 5⟩))
    (some (.ok (Array.replicate 5 (EmptyValue.mk 17))))
  check "empty slice skips decoding"
    (value ((readSlice RejectedEmpty 1 ⟨p, 0⟩).map Array.size)) (some (.ok 0))
  check "zero-sized slice preserves decoder errors"
    (value ((readSlice RejectedEmpty 1 ⟨p, 5⟩).map Array.size))
    (some (.error .unspecified))
  let untouched : MemM (Nat × Nat × Nat) := do
    memset (α := EmptyValue) 64 p 5 (some ⟨3⟩)
    memmove 0 64 64 p p 5
    let _ ← readSlice EmptyValue 64 ⟨p, 5⟩
    let m ← get
    pure (m.blocks.size, m.footprint.size, m.clocks[0]!.get 0)
  check "zero bytes leave memory and race clocks untouched" (value untouched) (some (.ok (0, 0, 0)))
  check "positive bytes still reject a provenance-free pointer"
    (value (memmove 1 1 1 p p 5)) (some (.error .illegal))

private def pointerTests : IO Unit := do
  let roundTrip : MemM (BitVec 8) := do
    let p ← alloc .heap 1 1
    store 1 p (42#8)
    let q ← ptrFromAddr (← ptrAddr (p.add 1)).toNat
    load (BitVec 8) 1 (q.add (-1))
  check "one-past round-trip followed by subtraction" (value roundTrip) (some (.ok 42#8))
  let endpoint : MemM (BitVec 8) := do
    let p ← alloc .heap 1 1
    let q ← ptrFromAddr (← ptrAddr (p.add 1)).toNat
    load (BitVec 8) 1 q
  check "one-past still cannot be dereferenced" (value endpoint) (some (.error .illegal))
  let gap : MemM (Option BlockId × Option BlockId × Bool) := do
    let p ← alloc .heap 1 1
    let p₂ ← alloc .heap 1 8
    let a ← ptrAddr p
    let endpoint ← ptrFromAddr (a + 1).toNat
    let gap ← ptrFromAddr (a + 2).toNat
    let start ← ptrFromAddr (← ptrAddr p₂).toNat
    pure (endpoint.block, gap.block, start = p₂)
  check "endpoint provenance and alignment gap" (value gap) (some (.ok (some 0, none, true)))
  let dead : MemM (Option BlockId) := do
    let p ← alloc .heap 1 1
    free p
    pure (← ptrFromAddr (← ptrAddr (p.add 1)).toNat).block
  check "dead endpoint keeps provenance" (value dead) (some (.ok (some 0)))
  let dangling : MemM (BitVec 8) := do
    let p ← alloc .heap 1 1
    free p
    let q ← ptrFromAddr (← ptrAddr (p.add 1)).toNat
    load (BitVec 8) 1 (q.add (-1))
  check "endpoint subtraction does not revive a freed block" (value dangling) (some (.error .illegal))

private def casWithPlain (readFirst succeeds plainWrite : Bool) : MemM (Option (BitVec 8)) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let child ← Thread.fork
  let plain : MemM Unit :=
    if plainWrite then store 1 p (42#8) else do let _ ← load (BitVec 8) 1 p; pure ()
  if readFirst then plain
  modify fun m => { m with current := child }
  let r ← cmpxchgAt 0 .relaxed .relaxed 1 p (if succeeds then 42#8 else 99#8) (7#8)
  modify fun m => { m with current := 0 }
  if !readFirst then plain
  pure r

private def casSummary (succeeds : Bool) : MemM
    (Option (BitVec 8) × Array AccessKind × Nat × Nat × Nat) := do
  let p ← alloc .heap 1 1
  store 1 p (42#8)
  let count := casCount 8 .relaxed 1 p (if succeeds then 42#8 else 99#8) (← get)
  let r ← cmpxchgAt 0 .relaxed .relaxed 1 p (if succeeds then 42#8 else 99#8) (7#8)
  let m ← get
  pure (r, m.footprint.map (·.kind), m.clocks[0]!.get 0, m.atomics[0]!.msgs.size, count)

private def casTests : IO Unit := do
  for first in [false, true] do
    check "failed CAS and concurrent plain read in either order"
      (value (casWithPlain first false false)) (some (.ok (some 42#8)))
    check "successful CAS and concurrent plain read in either order"
      (value (casWithPlain first true false)) (some (.error .illegal))
    check "failed CAS and concurrent plain write in either order"
      (value (casWithPlain first false true)) (some (.error .illegal))
  -- CAS is one scheduler operation; its successful branch records two internal accesses/ticks.
  let failedSummary := match value (casSummary false) with
    | some (.ok (some old, fp, 2, 1, 1)) =>
      match fp.toList with
      | [.write, .atomicRead] => old == 42#8
      | _ => false
    | _ => false
  check "failed CAS records one read and no message" failedSummary true
  let successfulSummary := match value (casSummary true) with
    | some (.ok (none, fp, 3, 2, 1)) =>
      match fp.toList with
      | [.write, .atomicRead, .atomicWrite] => true
      | _ => false
    | _ => false
  check "successful CAS records read then write and a new message" successfulSummary true
  let changed : MemM (BitVec 8) := do
    let p ← alloc .heap 1 1
    store 1 p (42#8)
    let _ ← cmpxchgAt 0 .relaxed .relaxed 1 p (42#8) (7#8)
    atomicLoadAt (n := 8) 0 .relaxed 1 p
  check "successful CAS writes the desired value" (value changed) (some (.ok 7#8))

private def childReadFree (joined sentinel destroy : Bool) : MemM (Bool × AccessKind × Nat) := do
  let p ← alloc .heap (if sentinel then 2 else 1) 1
  store 1 p (42#8)
  if sentinel then store 1 (p.add 1) (42#8)
  let child ← Thread.fork
  modify fun m => { m with current := child }
  let _ ← load (BitVec 8) 1 (if sentinel then p.add 1 else p)
  modify fun m => { m with current := 0 }
  if joined then Thread.join child
  if destroy then Allocator.destroy {} 1 p
  else if sentinel then Allocator.freeSentinel {} 1 ⟨p, 1⟩
  else Allocator.free {} 1 ⟨p, 1⟩
  let m ← get
  let some blk := m.blocks[0]? | throw .illegal
  pure (blk.live, m.footprint.back!.kind, m.footprint.back!.len)

private def freeTests : IO Unit := do
  check "slice poison write races with an unjoined child read"
    (value (childReadFree false false false *> pure ())) (some (.error .illegal))
  check "slice poison write succeeds after joining the child"
    (match value (childReadFree true false false) with
      | some (.ok (false, .write, 1)) => true
      | _ => false) true
  check "sentinel poison write includes the sentinel bytes"
    (value (childReadFree false true false *> pure ())) (some (.error .illegal))
  check "sentinel free succeeds after join and records the full block"
    (match value (childReadFree true true false) with
      | some (.ok (false, .write, 2)) => true
      | _ => false) true
  check "destroy retains rawFree semantics without a poison write"
    (match value (childReadFree false false true) with
      | some (.ok (false, .read, 1)) => true
      | _ => false) true
  check "zero byte free accepts the allocator's zero pointer"
    (value (Allocator.free {} 0 ⟨zeroAllocPtr 1, 5⟩)) (some (.ok ()))
  let bad : MemM Unit := do
    let p ← alloc .heap 2 1
    Allocator.free {} 1 ⟨p, 1⟩
  check "poison free still requires the whole heap block" (value bad) (some (.error .illegal))

end MemoryRegression

def main : IO Unit := do
  MemoryRegression.zeroTests
  MemoryRegression.pointerTests
  MemoryRegression.casTests
  MemoryRegression.freeTests
  IO.println "Memory regressions passed"
