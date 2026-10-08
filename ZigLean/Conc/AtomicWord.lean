import ZigLean.Conc.Call

/-!
# Unordered loads and pointer-valued atomics (`--allocator-model translated`)

Two extensions of the RC11 approximation of `ZigLean/Mem/Thread.lean`, admitted only under
`--allocator-model translated` (`docs/allocator-model.md`) for `std.heap.PageAllocator`'s
address hint (`@atomicLoad(?[*]u8, &addr_hint, .unordered)` and a `monotonic`
`@cmpxchgStrong` on it):

- **`unordered` loads.** LLVM's `unordered` has no per-location read-read coherence: a load
  may read any message that is not older than the newest one that happened before it. Unlike a
  `monotonic` read, it neither consults nor updates the thread's own read view (`Mem.seen`),
  and it never synchronizes. This admits every outcome a `monotonic` read admits, and more.
- **Pointer-valued atomics.** An 8-byte pointer or nullable pointer pointee (`Zig.Ptr`,
  `Option Zig.Ptr`) is read and written as its `Enc` bytes, so a message keeps the pointer's
  provenance (`Byte.ptrFrag`). A strong compare-exchange compares *addresses*, as the hardware
  does (`ptrBytesAddr`): `null` is address 0, a pointer without a block is its offset, a
  pointer into a block is the block's address plus the offset. A message whose bytes are not a
  pointer encoding never matches, and decoding it throws `.unspecified`.

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

/-- `atomic_load` (not `unordered`) of an 8-byte pointer value: option `c` of `loadCount 64`. -/
def atomicLoadEncAt (α : Type) [Enc α] (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    MemM α := do
  let (li, opts) ← loadPrep 64 ord align p false
  let some pos := opts[c]? | throw .illegal
  let msg := (← get).atomics[li]!.msgs[pos]!
  observe li msg.id
  if ord.isAcq then acquireClock msg.relClock
  Enc.decode msg.bytes

/-- The address that the 8 bytes `bs` of a pointer value hold, in `m`: `0` for `null` (eight
zero bytes), else the pointer's address (`ptrAddr`). `none`: not a pointer encoding, or a
block that does not exist. -/
def ptrBytesAddr (m : Mem) (bs : Array Byte) : Option Int :=
  if bs.extract 0 8 == Array.replicate 8 (.int 0) then some 0 else
  match (Enc.decode bs : Result Ptr).run with
  | some (.ok p) =>
    match p.block with
    | none => some p.off
    | some b => (m.blocks[b]?).map fun blk => (blk.addr : Int) + p.off
  | _ => none

/-- The pointer bytes `bs` and `expected` hold the same address in `m`. -/
def ptrBytesMatch (m : Mem) (bs expected : Array Byte) : Bool :=
  match ptrBytesAddr m bs, ptrBytesAddr m expected with
  | some a, some b => a == b
  | _, _ => false

/-- A strong pointer `cmpxchg`: the readable messages; one whose address matches `expected`
must have no RMW after it. -/
def casPtrPrep (align : Nat) (p : Ptr) (expected : Array Byte) : MemM (Nat × Array Nat) := do
  let (li, readable) ← casReadPrep 64 align p
  let m ← get
  let l := m.atomics[li]!
  pure (li, readable.filter fun pos =>
    !(l.hasRmwAfter pos && ptrBytesMatch m l.msgs[pos]!.bytes expected))

def casPtrCount (align : Nat) (p : Ptr) (expected : Array Byte) : Mem → Nat :=
  optCount ((·.2) <$> casPtrPrep align p expected)

/-- `rmwWrite` of the bytes `new` (a pointer encoding). -/
def rmwWriteBytes (li pos : Nat) (ord : AtomicOrder) (rd : Msg) (new : Array Byte) : MemM Unit := do
  if ord.isAcq then acquireClock rd.relClock
  let m ← get
  let cl := m.clocks[m.current]!
  let id := m.nextMsg
  let msg : Msg :=
    { id := id, bytes := new, clock := cl,
      relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock), rmwOf := some rd.id }
  insertMsg li (pos + 1) msg
  observe li id

/-- `cmpxchg_strong` of an 8-byte pointer value: option `c` of `casPtrCount`. `none` on
success (the store happened), `some` of the value read on failure. Never fails spuriously. -/
def cmpxchgEncAt (α : Type) [Enc α] (c : Nat) (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : α) : MemM (Option α) := do
  let (li, opts) ← casPtrPrep align p (Enc.encode expected)
  let some pos := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old : α ← Enc.decode rd.bytes
  if ptrBytesMatch (← get) rd.bytes (Enc.encode expected) then
    casMarkWrite 64 align p
    rmwWriteBytes li pos succ rd (Enc.encode new)
    pure none
  else
    observe li rd.id
    if fail.isAcq then acquireClock rd.relClock
    pure (some old)

variable {Tgt σ : Type}

def atomicLoadUnorderedC {n : Nat} (align : Nat) (p : Ptr) : CM Tgt σ (BitVec n) := do
  let c ← pickC (unorderedCount (intSize n) align p)
  callMC (atomicLoadUnorderedAt c align p)

def atomicLoadUnorderedEncC (α : Type) [Enc α] (align : Nat) (p : Ptr) : CM Tgt σ α := do
  let c ← pickC (unorderedCount 8 align p)
  callMC (atomicLoadUnorderedEncAt α c align p)

def atomicLoadEncC (α : Type) [Enc α] (ord : AtomicOrder) (align : Nat) (p : Ptr) : CM Tgt σ α := do
  let c ← pickC (loadCount 64 ord align p)
  callMC (atomicLoadEncAt α c ord align p)

def cmpxchgEncC (α : Type) [Enc α] (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : α) : CM Tgt σ (Option α) := do
  let c ← pickC (casPtrCount align p (Enc.encode expected))
  callMC (cmpxchgEncAt α c succ fail align p expected new)

end Zig
