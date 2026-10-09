import ZigLean.Conc.Call

/-!
# Unordered loads (`--allocator-model translated`)

An extension of the RC11 approximation of `ZigLean/Mem/Thread.lean`, admitted only under
`--allocator-model translated` (`docs/allocator-model.md`) for `std.heap.PageAllocator`'s
address hint (`@atomicLoad(?[*]u8, &addr_hint, .unordered)`).

LLVM's `unordered` has no per-location read-read coherence: a load may read any message that is
not older than the newest one that happened before it. Unlike a `monotonic` read, it neither
consults nor updates the thread's own read view (`Mem.seen`), and it never synchronizes. This
admits every outcome a `monotonic` read admits, and more. A pointer pointee (`Zig.Ptr`,
`Option Zig.Ptr`) is decoded from the message's bytes, which keep the pointer's provenance, as
for the other pointer atomics (`ZigLean/Mem/AtomicPtr.lean`).

Each op is an oracle choice (`pickC`) followed by the `MemM` op at that choice, as for the
integer ops (`ZigLean/Conc/Call.lean`).
-/

namespace Zig

/-- The oldest position an `unordered` read can read at location `li`: the newest message that
happened before the reader. The thread's earlier reads (`Mem.seen`) do not bound it. -/
def hbFloorPos (m : Mem) (li : Nat) : Nat :=
  let l := m.atomics[li]!
  let c := m.clocks[m.current]!
  l.msgs.zipIdx.foldl (fun a (x, i) => if VClock.le x.clock c then Nat.max a i else a) 0

/-- The positions an `unordered` read can read, newest first. -/
def unorderedOpts (m : Mem) (li : Nat) : Array Nat :=
  let n := (m.atomics[li]!).msgs.size
  let f := hbFloorPos m li
  (Array.range (n - f)).map fun k => n - 1 - k

/-- An `unordered` read of `size` bytes at `p`: the access, the race record, the location and
its options. -/
def unorderedPrep (size align : Nat) (p : Ptr) : MemM (Nat × Array Nat) := do
  let m ← get
  let (b, _, o) ← m.access p size align
  recordAccess b o size .atomicRead
  let li ← locIdx b o size
  pure (li, unorderedOpts (← get) li)

def unorderedCount (size align : Nat) (p : Ptr) : Mem → Nat :=
  optCount ((·.2) <$> unorderedPrep size align p)

/-- `atomic_load .unordered` of an `n`-bit integer: option `c` of `unorderedCount`. No
observation, no synchronization. -/
def atomicLoadUnorderedAt {n : Nat} (c : Nat) (align : Nat) (p : Ptr) : MemM (BitVec n) := do
  let (li, opts) ← unorderedPrep (intSize n) align p
  let some pos := opts[c]? | throw .illegal
  intOfBytes n ((← get).atomics[li]!.msgs[pos]!.bytes)

/-- `atomic_load .unordered` of an 8-byte pointer value. -/
def atomicLoadUnorderedEncAt (α : Type) [Enc α] (c : Nat) (align : Nat) (p : Ptr) : MemM α := do
  let (li, opts) ← unorderedPrep 8 align p
  let some pos := opts[c]? | throw .illegal
  Enc.decode ((← get).atomics[li]!.msgs[pos]!.bytes)

variable {Tgt σ : Type}

def atomicLoadUnorderedC {n : Nat} (align : Nat) (p : Ptr) : CM Tgt σ (BitVec n) := do
  let c ← pickC (unorderedCount (intSize n) align p)
  callMC (atomicLoadUnorderedAt c align p)

def atomicLoadUnorderedEncC (α : Type) [Enc α] (align : Nat) (p : Ptr) : CM Tgt σ α := do
  let c ← pickC (unorderedCount 8 align p)
  callMC (atomicLoadUnorderedEncAt α c align p)

end Zig
