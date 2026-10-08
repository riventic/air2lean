import ZigLean.Basic

/-!
# Byte-level memory

A CompCert-style memory: a list of blocks, each an array of bytes. A pointer is a block and a
byte offset, so a pointer stored in memory keeps its block (`Byte.ptrFrag`). Blocks are never
removed: `free` marks a block dead, and every later access to it throws `.illegal`.

A function that uses memory (`docs/generated-code.md` §Memory) returns `Zig.MemM α`, and its
body runs in `Zig.MM σ ε`. A pure function keeps `Zig.Result α` and `Zig.M σ ε`.

Each block gets an address when it is allocated: the next free address, rounded up to the
block's alignment, with at least 1 byte between two blocks, so one past the end of a block is
never the start of the next one. The alignment check of an access uses this address.
-/

namespace Zig

abbrev BlockId := Nat

/-- A pointer: a block and a byte offset into it. `block = none`: a pointer without a block;
every access through it throws `.illegal`. -/
structure Ptr where
  block : Option BlockId
  off : Int
  deriving DecidableEq, Repr, Inhabited

/-- The pointer `n` bytes after `p` (`struct_field_ptr`). -/
@[inline] def Ptr.add (p : Ptr) (n : Int) : Ptr := { p with off := p.off + n }

/-- The pointer to item `i` after `p`, for items of `size` bytes (`ptr_add`, `ptr_elem_ptr`). -/
@[inline] def Ptr.elem (p : Ptr) (size : Nat) (i : BitVec 64) : Ptr := p.add (size * i.toNat)

/-- The pointer to item `i` before `p` (`ptr_sub`). -/
@[inline] def Ptr.elemSub (p : Ptr) (size : Nat) (i : BitVec 64) : Ptr := p.add (-(size * i.toNat))

/-- A slice `[]T`: the pointer to item 0, and the item count. -/
structure Slice where
  ptr : Ptr
  len : BitVec 64
  deriving DecidableEq, Repr, Inhabited

inductive Byte where
  | undef
  | int (b : BitVec 8)
  /-- Byte `i` (little-endian) of the 8-byte pointer `p`. -/
  | ptrFrag (p : Ptr) (i : Fin 8)
  /-- Byte `i` of the code of the error `e`: 2 bytes by default, 1 to 4 bytes for the error
  integer that `--error-limit` selects (`ZigLean/Mem/ErrWidth.lean`). The compiler numbers the
  errors per compilation, so the model keeps the name, as `ptrFrag` keeps the pointer (M20). -/
  | errFrag (e : ErrName) (i : Fin 4)
  /-- The low `m` bits of `b` are defined (`0 < m < 8`, `b`'s bits above are 0); the bits above
  are undefined: the last byte of a `uN` with `N % 8 ≠ 0` (`intBytes`). A read that needs a
  bit above `m` throws `.unspecified` (`intOfBytes`). -/
  | part (m : Nat) (b : BitVec 8)
  /-- The bits set in `d` are defined, with the values of `b`; the others are undefined (`b`'s
  bits there are 0). Only for a mask that is not all, none or the low bits (`.int`, `.undef`,
  `.part`): a bit-pointer store of a field or of `undefined` next to undefined bits
  (`Byte.ofDefBits`, `ZigLean/Packed.lean`). A read that needs a bit outside `d` throws
  `.unspecified` (`intOfBytes`). -/
  | mask (d b : BitVec 8)
  deriving DecidableEq, Repr, Inhabited

/-- The identity of an allocator other than the model's `std.mem.Allocator`: an index into
`Mem.allocators`. -/
abbrev AllocId := Nat

inductive BlockKind where
  | stack
  | heap
  | global
  /-- A `const` global, a string literal or a function: read-only. A write to it (through
  `@constCast`) throws `.illegal`. -/
  | constGlobal
  /-- A block that the allocator `a` made: an arena or a fixed buffer (`Mem.allocators[a]`,
  `ZigLean/Mem/Owned.lean`). A `.heap` block is one of the model's `std.mem.Allocator`, so a
  free through one allocator of a block that another one made throws `.illegal`. -/
  | owned (a : AllocId)
  deriving DecidableEq, Repr

structure Block where
  bytes : Array Byte
  align : Nat
  kind : BlockKind
  live : Bool
  /-- The address of byte 0 (`@intFromPtr`). -/
  addr : Nat
  deriving Repr

/-! ## Threads (`ZigLean/Mem/Thread.lean`, `docs/std-models.md` §Thread model)

Fork-join only: `std.Thread.spawn`/`.join`. Thread 0 is the thread the top-level call runs on;
every other id is a spawned thread, in spawn order. `Mem.clocks`/`Mem.threads` are indexed by
`ThreadId` and always the same size. -/

abbrev ThreadId := Nat

/-- A Lamport vector clock: component `i` is how many of thread `i`'s own recorded accesses the
clock's owner has observed (its own, plus every other thread's up to the last fork/join edge
with it). -/
abbrev VClock := Array Nat

namespace VClock

def get (c : VClock) (i : ThreadId) : Nat := c.getD i 0

/-- Bump `t`'s own component: one more of `t`'s own accesses. -/
def bump (c : VClock) (t : ThreadId) : VClock :=
  let c := if t < c.size then c else c ++ Array.replicate (t + 1 - c.size) 0
  c.set! t (c.get t + 1)

/-- Component-wise max: what a thread adopts when it observes another (a join edge). -/
def merge (a b : VClock) : VClock :=
  (Array.range (Nat.max a.size b.size)).map fun i => Nat.max (a.get i) (b.get i)

/-- `a` happened-before-or-equal `b`: every component of `a` is `≤` the same component of `b`. -/
def le (a b : VClock) : Bool :=
  (Array.range (Nat.max a.size b.size)).all fun i => Nat.ble (a.get i) (b.get i)

/-- Neither happened-before the other: two accesses with concurrent clocks are a race candidate
if their byte ranges overlap (`recordAccess`). -/
def concurrent (a b : VClock) : Bool := !le a b && !le b a

end VClock

/-- One memory access, for the race check. -/
inductive AccessKind where
  | read
  | write
  | atomicRead
  | atomicWrite
  deriving Repr, Inhabited, DecidableEq

def AccessKind.isWrite : AccessKind → Bool
  | .write | .atomicWrite => true
  | _ => false

def AccessKind.isAtomic : AccessKind → Bool
  | .atomicRead | .atomicWrite => true
  | _ => false

/-- `none`: `a` and `b`, both touching the same bytes with concurrent clocks, do not race.
`some .illegal`: a data race (C11): at least one is a write and at least one is not atomic. Two
atomic accesses never race: the scheduler orders them (`ZigLean/Conc/Sched.lean`). -/
def racePair (a b : AccessKind) : Option Error :=
  if (a.isWrite || b.isWrite) && !(a.isAtomic && b.isAtomic) then some .illegal else none

/-- Who spawned thread `id` (the parent thread's own `ThreadId` at the time), and whether
`Thread.join` has run on it. Index 0 (main) is unused: nothing ever joins it. -/
structure ThreadRec where
  spawner : ThreadId
  joined : Bool
  deriving Repr, Inhabited

/-- One recorded access, kept so a later overlapping access can check it for a race. -/
structure FootprintEntry where
  tid : ThreadId
  clock : VClock
  block : BlockId
  off : Nat
  len : Nat
  kind : AccessKind
  deriving Repr, Inhabited

/-- The ordering of an atomic op (`std.builtin.AtomicOrder`; `unordered` is outside the
subset). -/
inductive AtomicOrder where
  | relaxed | acquire | release | acqRel | seqCst
  deriving DecidableEq, Repr, Inhabited

def AtomicOrder.isAcq : AtomicOrder → Bool
  | .acquire | .acqRel | .seqCst => true
  | _ => false

def AtomicOrder.isRel : AtomicOrder → Bool
  | .release | .acqRel | .seqCst => true
  | _ => false

/-- One write to an atomic location (RC11, `ZigLean/Mem/Thread.lean`). -/
structure Msg where
  id : Nat
  bytes : Array Byte
  /-- The writer's clock at the write: the write happened before a thread whose clock is `≥`
  it. -/
  clock : VClock
  /-- The clock that an acquire read of this message adopts: the writer's clock for a release
  write, joined along a release sequence (the RMWs after it); empty otherwise. -/
  relClock : VClock
  /-- For an RMW: the id of the message it read. It stays right after that message. -/
  rmwOf : Option Nat := none
  deriving Repr, Inhabited

/-- An atomic location: its writes in modification order. -/
structure ALoc where
  block : BlockId
  off : Nat
  len : Nat
  msgs : Array Msg
  deriving Repr, Inhabited

/-- The differential harness's request cap (1 MiB), the legacy model default. It is selected
explicitly (`AllocPolicy.harness`); the model default has no fixed cap. -/
def maxAllocBytes : Nat := 1 <<< 20

/-- No fixed model cap: every `usize` request (fewer than 2^64 bytes) passes the size check. -/
def unboundedAllocBytes : Nat := 2 ^ 64

/-- Explicit byte-remap environment. Default failure preserves the legacy allocator.
Successful policies cover only nonempty, alignment-1 byte buffers. -/
inductive ByteRemapMode where
  | fail | inPlace | move
  deriving DecidableEq, Repr, Inhabited

/-- Selected allocator environment: a per-request cap, finite failure indices, an arbitrary
failure oracle over (attempt index, request bytes) and an optional live-heap budget.
The cap and finite list are special cases of the oracle (`AllocPolicy.asOracle` in
`ZigLean.Sep.Alloc`).
It is not a claim about a native allocator's available memory or address policy. -/
structure AllocPolicy where
  maxBytes : Nat := unboundedAllocBytes
  failures : List Nat := []
  byteRemap : ByteRemapMode := .fail
  /-- Arbitrary permitted failure decisions: `fails i n` fails attempt `i` of `n` bytes. -/
  fails : Nat → Nat → Bool := fun _ _ => false
  /-- Total live-heap bytes allowed after the request; `none` is unbounded. -/
  budget : Option Nat := none
  deriving Inhabited

/-- The oracle is a function, so it is shown opaquely. -/
instance : Repr AllocPolicy where
  reprPrec p _ := f!"\{ maxBytes := {repr p.maxBytes}, failures := {repr p.failures}, " ++
    f!"byteRemap := {repr p.byteRemap}, fails := <oracle>, budget := {repr p.budget} }"

/-- The differential harness policy: the legacy 1 MiB request cap and no other failures. -/
def AllocPolicy.harness : AllocPolicy := { maxBytes := maxAllocBytes }

/-- The kind of an allocator with an identity (`ZigLean/Mem/Owned.lean`, M01). -/
inductive OwnedPolicy where
  /-- `std.heap.ArenaAllocator` over the model's `std.mem.Allocator`. -/
  | arena
  /-- `std.heap.FixedBufferAllocator` over a buffer of `cap` bytes at address `base`. -/
  | fixedBuffer (base cap : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The state of an allocator with an identity. -/
structure OwnedAlloc where
  policy : OwnedPolicy
  /-- `false` after `ArenaAllocator.deinit`: every later use throws `.illegal`. -/
  live : Bool := true
  /-- `FixedBufferAllocator.end_index`. -/
  used : Nat := 0
  /-- The buffer index of the first byte of each block of a fixed buffer, for its
  `isLastAllocation`. -/
  starts : List (BlockId × Nat) := []
  deriving DecidableEq, Repr, Inhabited

structure Mem where
  blocks : Array Block := #[]
  /-- The lowest address that the next block can get. Never 0. -/
  nextAddr : Nat := 4096
  /-- The number of allocations so far (`Zig.rawAlloc`, `ZigLean/Mem/Alloc.lean`). -/
  allocs : Nat := 0
  /-- The allocation that fails: allocation number `failAt` (from 0), or none. -/
  failAt : Option Nat := none
  /-- Additional failures and the request-size bound. Defaults preserve the legacy model. -/
  allocPolicy : AllocPolicy := {}
  /-- The thread that is running right now. -/
  current : ThreadId := 0
  /-- `clocks[t]`: thread `t`'s own vector clock. Same size as `threads`. -/
  clocks : Array VClock := #[#[]]
  /-- `threads[t]`: bookkeeping for thread `t`, `t > 0` (`ZigLean/Mem/Thread.lean`). -/
  threads : Array ThreadRec := #[{ spawner := 0, joined := true }]
  /-- Every access recorded so far, across every thread. -/
  footprint : Array FootprintEntry := #[]
  /-- The atomic locations (RC11, `ZigLean/Mem/Thread.lean`). -/
  atomics : Array ALoc := #[]
  /-- `(t, loc, id)`: the last message of atomic location `loc` that thread `t` read or wrote. -/
  seen : Array (ThreadId × Nat × Nat) := #[]
  /-- The id of the next message. -/
  nextMsg : Nat := 0
  /-- The futex queue (the kernel's state, `ZigLean/Mem/Thread.lean`): the threads that wait at
  a futex, and the address, in the order they began to wait. -/
  waiters : Array (ThreadId × Ptr) := #[]
  /-- The threads that a futex wake woke: their wait goes on at their next turn. -/
  woken : Array ThreadId := #[]
  /-- The tasks of each `Io.Group` (by its address) that no `await` has joined yet, in the order
  of their spawn (`ZigLean/Mem/Thread.lean`). -/
  groups : Array (Ptr × ThreadId) := #[]
  /-- The allocators with an identity, by `AllocId` (`ZigLean/Mem/Owned.lean`). -/
  allocators : Array OwnedAlloc := #[]
  /-- The thread-assignment budget of the `fallible` spawn policy (`ZigLean/Conc/Spawn.lean`):
  at most this many assigned child threads that no join has reclaimed. `none` (the default) sets
  no budget. The `available` policy ignores it. -/
  spawnLimit : Option Nat := none
  deriving Repr, Inhabited

/-- The state of a function that uses memory. -/
abbrev MemM (α : Type) := StateT Mem Result α

/-- The body monad of a function that uses memory: its locals over `MemM`. -/
abbrev MM (σ α : Type) := StateT σ MemM α

/-- `n` rounded up to a multiple of `a` (`a = 0`: `n`). -/
def alignUp (n a : Nat) : Nat := if a = 0 then n else (n + a - 1) / a * a

/-- The block and the offset of an access of `n` bytes at `p` that needs alignment `align`.
Throws `.illegal` if the block is dead, the bytes are not all in the block, or the address is
not a multiple of `align`. -/
def Mem.access (m : Mem) (p : Ptr) (n align : Nat) : Result (BlockId × Block × Nat) :=
  match p.block with
  | none => throw .illegal
  | some b =>
    match m.blocks[b]? with
    | none => throw .illegal
    | some blk =>
      if blk.live ∧ 0 ≤ p.off ∧ p.off + n ≤ blk.bytes.size ∧ (blk.addr + p.off.toNat) % align = 0
      then pure (b, blk, p.off.toNat) else throw .illegal

/-- `Mem.access` for a write: a write to a `const` global throws `.illegal`. -/
def Mem.accessW (m : Mem) (p : Ptr) (n align : Nat) : Result (BlockId × Block × Nat) := do
  let r ← m.access p n align
  if r.2.1.kind = .constGlobal then throw .illegal else pure r

/-- `a` with the bytes from offset `o` on replaced by `bs` (`o + bs.size ≤ a.size`). -/
def writeBytes (a : Array Byte) (o : Nat) (bs : Array Byte) : Array Byte :=
  a.extract 0 o ++ bs ++ a.extract (o + bs.size) a.size

/-- The race error of the first (chronologically earliest) footprint entry of `fp` that overlaps
`block`/`off`/`len` with a concurrent clock and races with `kind` (`racePair`); `none` if no
entry races. `Array.findSome?` searches in order, so this matches recording the accesses one at a
time and stopping at the first conflict. -/
def raceAt (fp : Array FootprintEntry) (clock : VClock) (block : BlockId) (off len : Nat)
    (kind : AccessKind) : Option Error :=
  fp.findSome? fun e =>
    if e.block == block && off < e.off + e.len && e.off < off + len &&
        VClock.concurrent e.clock clock then racePair e.kind kind
    else none

/-- Record one access at `block`/`off`/`len` by the current thread (`ZigLean/Mem/Thread.lean`),
checking it against every earlier overlapping access from a concurrent thread (`racePair`, via
`raceAt`). Throws the race's error before recording anything. -/
def recordAccess (block : BlockId) (off len : Nat) (kind : AccessKind) : MemM Unit := do
  let m ← get
  let t := m.current
  let clock := VClock.bump (m.clocks[t]!) t
  match raceAt m.footprint clock block off len kind with
  | some err => throw err
  | none =>
    set { m with
      clocks := m.clocks.set! t clock,
      footprint := m.footprint.push { tid := t, clock, block, off, len, kind } }

def loadBytes (p : Ptr) (n align : Nat) (kind : AccessKind := .read) : MemM (Array Byte) := do
  let (b, blk, o) ← (← get).access p n align
  recordAccess b o n kind
  pure (blk.bytes.extract o (o + n))

/-- A genuinely unused AIR load still reads its entire byte range, checking provenance,
bounds, alignment and races. Its bytes are not decoded into an unused typed value. -/
def loadDiscardBytes (n align : Nat) (p : Ptr) : MemM Unit := do
  let (b, _, o) ← (← get).access p n align
  recordAccess b o n .read
  pure ()

def storeBytes (p : Ptr) (align : Nat) (bs : Array Byte) (kind : AccessKind := .write) : MemM Unit := do
  let m ← get
  let (b, blk, o) ← m.accessW p bs.size align
  recordAccess b o bs.size kind
  let m ← get
  set { m with blocks := m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs } }

/-- A new block of `size` undefined bytes. -/
def alloc (kind : BlockKind) (size align : Nat) : MemM Ptr := do
  let m ← get
  let addr := alignUp m.nextAddr align
  set { m with
    blocks := m.blocks.push { bytes := Array.replicate size .undef, align, kind, live := true, addr }
    nextAddr := addr + size + 1 }
  pure ⟨some m.blocks.size, 0⟩

/-- Free the block that `p` points to the start of. A dead block or an inner pointer throws
`.illegal`. -/
def free (p : Ptr) : MemM Unit := do
  let m ← get
  match p.block with
  | none => throw .illegal
  | some b =>
    match m.blocks[b]? with
    | some blk =>
      if blk.live ∧ p.off = 0 then set { m with blocks := m.blocks.set! b { blk with live := false } }
      else throw .illegal
    | none => throw .illegal

/-- The stack block of a local whose address escapes: made at function entry. -/
@[inline] def allocStack (size align : Nat) : MemM Ptr := alloc .stack size align

/-! ## Typed access -/

/-- The memory encoding of a Lean type: its size and alignment in bytes (the Zig ABI values),
and the bytes of a value. `decode` throws `.unspecified` if a byte that the value uses is
undefined; padding bytes are ignored. -/
class Enc (α : Type) where
  size : Nat
  align : Nat
  encode : α → Array Byte
  decode : Array Byte → Result α

/-- `load`/`store` take the alignment of the pointer type (`*align(N) T`), which can differ from
the type's own alignment. -/
def load (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM α := do
  let bs ← loadBytes p (Enc.size α) align
  Enc.decode bs

def store {α : Type} [Enc α] (align : Nat) (p : Ptr) (v : α) : MemM Unit :=
  storeBytes p align (Enc.encode v)

/-- `is_non_null_ptr` for `?T`, `T` not a pointer: the flag byte after the payload. -/
def optIsSome (α : Type) [Enc α] (p : Ptr) : MemM Bool := do
  match ((← loadBytes (p.add (Enc.size α)) 1 1)[0]? : Option Byte) with
  | some (.int x) => if x = 0 then pure false else if x = 1 then pure true else throw .illegal
  | _ => throw .unspecified

/-- `optional_payload_ptr_set` for `?T`, `T` not a pointer: set the flag byte; the payload is at
offset 0. -/
def optSetSome (α : Type) [Enc α] (p : Ptr) : MemM Ptr := do
  storeBytes (p.add (Enc.size α)) 1 #[.int 1]
  pure p

/-- A store of `undefined`: every byte of the value becomes undefined. -/
def storeUndef (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM Unit :=
  storeBytes p align (Array.replicate (Enc.size α) .undef)

/-! ## Values with undefined parts

A local that receives a store of `undefined` holds the bytes of its value (`Enc`), so that its
undefined parts stay undefined bytes: a store writes bytes, a read of a part decodes only the
part's bytes and throws `.unspecified` if one of them is undefined. A copy of the whole value
(a load returned or stored to memory) moves the bytes without decoding them. -/

/-- The bytes of a value of type `α` that can have undefined parts. -/
abbrev Bytes (_α : Type) := Array Byte

/-- Every byte undefined. -/
def Bytes.undef (α : Type) [Enc α] : Bytes α := Array.replicate (Enc.size α) .undef

/-- The bytes at `off` hold `v`. -/
def Bytes.set {α β : Type} [Enc β] (bs : Bytes α) (off : Nat) (v : β) : Bytes α :=
  writeBytes bs off (Enc.encode v)

/-- The bytes of a `β` at `off` become undefined. -/
def Bytes.setUndef {α : Type} (β : Type) [Enc β] (bs : Bytes α) (off : Nat) : Bytes α :=
  writeBytes bs off (Array.replicate (Enc.size β) .undef)

/-- The bytes at `off` become `src`'s (a copy of a value with undefined parts). -/
def Bytes.copy {α β : Type} (bs : Bytes α) (off : Nat) (src : Bytes β) : Bytes α :=
  writeBytes bs off src

/-- The `β` at `off`: throws `.unspecified` if one of its bytes is undefined. -/
def Bytes.get (β : Type) [Enc β] {α : Type} (bs : Bytes α) (off : Nat) : Result β :=
  Enc.decode (bs.extract off (off + Enc.size β))

/-! ## Memory ops

`@memset`, `@memcpy` and `@memmove` do nothing for 0 bytes (0 items or a zero-sized item), also through a pointer
that is not valid. For more items, the access is checked before the bytes are made. -/

/-- `@memset`: each of the `n` items at `p` becomes `v`. `v = none`: `undefined`, every byte of
the items becomes undefined. -/
def memset {α : Type} [Enc α] (align : Nat) (p : Ptr) (n : BitVec 64) (v : Option α) :
    MemM Unit := do
  if n.toNat = 0 ∨ Enc.size α = 0 then return
  let _ ← (← get).access p (n.toNat * Enc.size α) align
  let item := match v with
    | some x => Enc.encode x
    | none => Array.replicate (Enc.size α) .undef
  storeBytes p align (Array.replicate n.toNat item).flatten

/-- `@memcpy` and `@memmove`: copy `n` items of `size` bytes from `src` to `dst`. All bytes are
read before the first write, so an overlap copies the old bytes (`@memmove`). For `@memcpy`, the
AIR checks before that the two ranges do not overlap. -/
def memmove (size dstAlign srcAlign : Nat) (dst src : Ptr) (n : BitVec 64) : MemM Unit := do
  if n.toNat = 0 ∨ size = 0 then return
  let _ ← (← get).access dst (n.toNat * size) dstAlign
  let bs ← loadBytes src (n.toNat * size) srcAlign
  storeBytes dst dstAlign bs

/-- The items of `s`, for a call to a pure function with a `[]const T` parameter. An undefined
byte in any item throws `.unspecified`, also in an item that the function does not read.
Zero-sized items are decoded from empty bytes without accessing the slice pointer. -/
def readSlice (α : Type) [Enc α] (align : Nat) (s : Slice) : MemM (Array α) := do
  if s.len.toNat = 0 then return #[]
  let bs ← if Enc.size α = 0 then pure #[] else
    loadBytes s.ptr (s.len.toNat * Enc.size α) align
  (Array.range s.len.toNat).mapM fun i =>
    (Enc.decode (bs.extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)

/-- The address of `p`: the address of its block plus the offset. A pointer without a block has
the address `p.off`. -/
def ptrAddr (p : Ptr) : MemM Int := do
  match p.block with
  | none => pure p.off
  | some b =>
    match (← get).blocks[b]? with
    | some blk => pure (blk.addr + p.off)
    | none => throw .illegal

/-- The pointer to address `n`: inside or one past the block whose address range covers `n`, at the matching
offset, or `⟨none, n⟩` if no block covers it (`@ptrFromInt`). A dead block still counts (its
`addr` does not change on `free`), so the pointer this returns can still be a dangling one; the
existing liveness check in `Mem.access` catches a later access through it. Round-trips with
`ptrAddr`: `ptrFromAddr (← ptrAddr p) = p` for `p` inside or one past its block's bytes. -/
def ptrFromAddr (n : Nat) : MemM Ptr := do
  let m ← get
  match m.blocks.zipIdx.findSome? fun (blk, b) =>
      if blk.addr ≤ n ∧ n ≤ blk.addr + blk.bytes.size then some (b, blk.addr) else none with
  | some (b, addr) => pure ⟨some b, (n : Int) - (addr : Int)⟩
  | none => pure ⟨none, n⟩

/-- `<`, `<=`, `>`, `>=` on pointers compare the addresses. Two blocks have the order of their
addresses in the model, which can differ from the compiled code. -/
def ptrLt (a b : Ptr) : MemM Bool := do pure (decide ((← ptrAddr a) < (← ptrAddr b)))
def ptrLe (a b : Ptr) : MemM Bool := do pure (decide ((← ptrAddr a) ≤ (← ptrAddr b)))

/-! ## Globals -/

/-- `m` with one more global block: `bytes` at the next free address, aligned to `align`.
`kind`: `.global` for a `var`, `.constGlobal` for anything else. -/
def Mem.addGlobal (m : Mem) (bytes : Array Byte) (align : Nat) (kind : BlockKind) : Mem :=
  let addr := alignUp m.nextAddr align
  { blocks := m.blocks.push { bytes, align, kind, live := true, addr }
    nextAddr := addr + bytes.size + 1 }

/-- The memory at program start: block `k` is global `k`, with its initial bytes, alignment
and kind. -/
def Mem.ofGlobals (gs : List (Array Byte × Nat × BlockKind)) : Mem :=
  gs.foldl (fun m (bs, a, k) => m.addGlobal bs a k) {}

/-! ## Calls -/

/-- A call from a function that uses memory to another one. -/
@[inline] def callM {σ α : Type} (r : MemM α) : MM σ α := StateT.lift r

/-- A call from a function that uses memory to a pure function. -/
@[inline] def callR {σ α : Type} (r : Result α) : MM σ α := StateT.lift (StateT.lift r)

section Monotone
open Lean.Order

/-- `callM` for `partial_fixpoint`, as `monotone_call` for `call` (`ZigLean/Basic.lean`). -/
@[partial_fixpoint_monotone]
theorem monotone_callM {σ α γ : Type} [PartialOrder γ]
    (f : γ → MemM α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callM (f x) : MM σ α)) := by
  apply monotone_of_monotone_apply
  intro s
  show monotone (fun x => (f x) >>= fun a => pure (a, s))
  exact monotone_bind _ _ _ hmono (monotone_const _)

/-- `monotone_run'` (`ZigLean/Basic.lean`) for a function that uses memory. -/
@[partial_fixpoint_monotone]
theorem monotone_runMM' {σ α γ : Type} [PartialOrder γ]
    (f : γ → MM σ α) (hmono : monotone f) (s : σ) :
    monotone (fun (x : γ) => (f x).run' s) := by
  have h := Functor.monotone_map (fun x => StateT.run (f x) s) (·.1) (monotone_stateTRun f hmono s)
  simpa [StateT.run', StateT.run] using h

/-- `monotone_loop` (`ZigLean/Basic.lean`) for a function that uses memory. -/
@[partial_fixpoint_monotone]
theorem monotone_loopMM {σ ε γ : Type} [PartialOrder γ] (f : γ → MM σ ε) (again : ε → Bool)
    (hmono : monotone f) : monotone (fun (x : γ) => loop (f x) again) := by
  intro x1 x2 hx
  have hle : f x1 ⊑ f x2 := hmono x1 x2 hx
  apply loop.fixpoint_induct (f x1) again (motive := fun v => v ⊑ loop (f x2) again)
  · exact fun _ hc h => csup_le hc h
  · intro l hl
    rw [loop.eq_1 (f x2) again]
    apply PartialOrder.rel_trans (MonoBind.bind_mono_left hle)
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact hl
    · exact PartialOrder.rel_refl

end Monotone

end Zig
