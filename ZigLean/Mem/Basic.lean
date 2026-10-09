import ZigLean.Basic
import ZigLean.Env.Host

/-!
# Byte-level memory

A CompCert-style memory: a list of blocks, each an array of bytes. A pointer is a block and a
byte offset, so a pointer stored in memory keeps its block (`Byte.ptrFrag`). Blocks are never
removed: `free` marks a block dead, and every later access to it throws `.illegal`.

A function that uses memory (`docs/generated-code.md` §Memory) returns `Zig.MemM α`, and its
body runs in `Zig.MM σ ε`. A pure function keeps `Zig.Result α` and `Zig.M σ ε`.

Each block gets an address when it is allocated: the next free address, rounded up to the
block's alignment, with at least 1 byte between two blocks, so one past the end of a block is
never the start of the next one. The alignment check of an access uses this address. An
opt-in policy (`AllocPolicy.reuseAddr`, M05) lets a heap or owned block reuse the address of a
freed block instead; block ids stay unique, and every lifetime check uses the block id, not the
address (`docs/address-reuse.md`).
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

/-- Who owns the join handle of thread `id`: the thread that spawned it, until an explicit
`Thread.transferHandle` (C07) moves it; and whether the handle was consumed, by `Thread.join` or
by `Thread.detach` (a detached thread may still run). Index 0 (main) is unused: nothing ever
joins it. `tls`: the thread's own instance of each `threadlocal` global, as
`(key, instance block)` (`ZigLean/Mem/Tls.lean`); empty for a program without `threadlocal`
globals and for a thread that has not started. -/
structure ThreadRec where
  spawner : ThreadId
  joined : Bool
  tls : Array (BlockId × BlockId) := #[]
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

/-- How `@ptrFromInt` recovers a provenance when more than one block's address range covers
the address (`ptrFromAddr`). That happens only under address reuse (`AllocPolicy.reuseAddr`,
`docs/address-reuse.md`): a freed block and a later block at its address. -/
inductive ProvenanceMode where
  /-- The default: the integer does not say which block it came from, so the recovery throws
  `.unspecified`. A stale integer never gains the provenance of the block that reuses its
  address. -/
  | strict
  /-- The address-sensitive contract: the address recovers the provenance of the live block that
  covers it (live blocks never share an address). A program that declares it asserts that each
  integer it converts belongs to that block, also a stale one. -/
  | liveBlock
  deriving DecidableEq, Repr, Inhabited

/-- Selected allocator environment: a per-request cap, finite failure indices, an arbitrary
failure oracle over (attempt index, request bytes) and an optional live-heap budget.
The cap and finite list are special cases of the oracle (`AllocPolicy.asOracle` in
`ZigLean.Sep.Alloc`).
It is not a claim about a native allocator's available memory. Its address policy is an
explicit, opt-in parameter too (`reuseAddr`, M05). -/
structure AllocPolicy where
  maxBytes : Nat := unboundedAllocBytes
  failures : List Nat := []
  byteRemap : ByteRemapMode := .fail
  /-- Arbitrary permitted failure decisions: `fails i n` fails attempt `i` of `n` bytes. -/
  fails : Nat → Nat → Bool := fun _ _ => false
  /-- Total live-heap bytes allowed after the request; `none` is unbounded. -/
  budget : Option Nat := none
  /-- Address reuse (M05, `docs/address-reuse.md`): `reuseAddr b` proposes the address of block
  `b`, a new heap or owned block. `alloc` takes it if it is a valid reuse (`Mem.reuseOk`): for
  example the address of a freed block. The default proposes nothing: every block gets a fresh
  address. Block ids stay unique either way. -/
  reuseAddr : BlockId → Option Nat := fun _ => none
  /-- `@ptrFromInt` of an address that more than one block covers (only under reuse). -/
  provenance : ProvenanceMode := .strict
  deriving Inhabited

/-- The oracles are functions, so they are shown opaquely. -/
instance : Repr AllocPolicy where
  reprPrec p _ := f!"\{ maxBytes := {repr p.maxBytes}, failures := {repr p.failures}, " ++
    f!"byteRemap := {repr p.byteRemap}, fails := <oracle>, budget := {repr p.budget}, " ++
    f!"reuseAddr := <oracle>, provenance := {repr p.provenance} }"

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

/-! ## Device effects (L13, `ZigLean/Mem/Device.lean`, `docs/volatile-effects.md`)

Only the opt-in device semantics (`air2lean --device-contract`) reads or writes `Mem.dev`. The
default translation rejects every volatile access, so its programs never touch it. -/

/-- One observable device event: a volatile load (`read`) or store (`write`) of a declared
register `bits` wide at address `addr`, with the value read or written. -/
inductive DevEvent where
  | read (addr bits value : Nat)
  | write (addr bits value : Nat)
  /-- A declared `asm volatile` (by its template) with its register inputs and its output
  (`bits = 0`, `value = 0`: no output). -/
  | asm (template : String) (inputs : List Nat) (bits value : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The device's answer to a volatile read of `bits` bits at `addr`, given every event so far
(oldest first). It is arbitrary: a theorem quantifies over it. `none`: the device gives no
answer, and the read throws `.unspecified`. -/
abbrev DevOracle := List DevEvent → Nat → (bits : Nat) → Option (BitVec bits)

/-- The device's answer to a declared `asm volatile` with the template and register inputs,
given every event so far. -/
abbrev AsmOracle := List DevEvent → String → List Nat → (bits : Nat) → Option (BitVec bits)

/-- The environment and the observable trace of the device effects. -/
structure DevState where
  /-- The default oracle never answers: a device read needs an explicitly chosen oracle. -/
  oracle : DevOracle := fun _ _ _ => none
  /-- The same for the outputs of declared asm; the default never answers either. -/
  asmOracle : AsmOracle := fun _ _ _ _ => none
  /-- Every device event so far, in program order (oldest first). -/
  trace : List DevEvent := []
  deriving Inhabited

/-- The oracle is a function, so it is shown opaquely. -/
instance : Repr DevState where
  reprPrec d _ := f!"\{ oracle := <oracle>, asmOracle := <oracle>, trace := {repr d.trace} }"

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
  /-- The `Io` tasks with a cancelation request (`Io.Group.cancel`, `Io.Future.cancel`) that no
  cancelation point has delivered yet (`ZigLean/Mem/Thread.lean`, `ZigLean/Conc/Future.lean`,
  `docs/std-models.md` §Cancelation). Empty in every program without a cancel. -/
  cancels : Array ThreadId := #[]
  /-- The device oracle and the trace of device events (`ZigLean/Mem/Device.lean`). -/
  dev : DevState := {}
  /-- The installed environment of the bound OS primitives (`ZigLean/Env/Linux.lean`, E03). The
  default has no open handle, so a program that never calls one is unaffected. -/
  host : Env.Host := {}
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

/-- No live block's address range meets `[A, A + n]` (one past the end included), so a block of
`n` bytes at `A` keeps at least 1 byte from every live block. Dead blocks do not count. -/
def Mem.addrFree (m : Mem) (A n : Nat) : Bool :=
  m.blocks.all fun blk => !blk.live || decide (A + n < blk.addr) || decide (blk.addr + blk.bytes.size < A)

/-- `A` is a valid reused address for a new block of `size` bytes with alignment `align`: not 0,
aligned, below `nextAddr` (so it stays below every later fresh block) and clear of every live
block (`Mem.addrFree`). It may be the address of a dead block. -/
def Mem.reuseOk (m : Mem) (A size align : Nat) : Bool :=
  decide (0 < A) && decide (A % align = 0) && decide (A + size < m.nextAddr) && m.addrFree A size

/-- The reused address of a new block of kind `kind` (M05): the policy's proposal
(`AllocPolicy.reuseAddr`) for the next block id, if it is valid (`Mem.reuseOk`). Stack blocks
and globals always get fresh addresses; heap and owned (allocator) blocks may reuse one. -/
def Mem.reuseAddr? (m : Mem) (kind : BlockKind) (size align : Nat) : Option Nat :=
  match kind with
  | .heap | .owned _ =>
    match m.allocPolicy.reuseAddr m.blocks.size with
    | some A => if m.reuseOk A size align then some A else none
    | none => none
  | _ => none

/-- The address of a new block: the reused one (`Mem.reuseAddr?`), or the next free address,
rounded up to `align`. Inlined with `Mem.newNext`, so compiled code evaluates the reuse
decision once per allocation. -/
@[inline] def Mem.newAddr (m : Mem) (kind : BlockKind) (size align : Nat) : Nat :=
  match m.reuseAddr? kind size align with
  | some A => A
  | none => alignUp m.nextAddr align

/-- `nextAddr` after a new block: unchanged for a reused address, else past the new block and
1 more byte. -/
@[inline] def Mem.newNext (m : Mem) (kind : BlockKind) (size align : Nat) : Nat :=
  match m.reuseAddr? kind size align with
  | some _ => m.nextAddr
  | none => alignUp m.nextAddr align + size + 1

/-- The memory after `alloc`: one more block, `m.blocks.size`, at `Mem.newAddr`. -/
def Mem.afterAlloc (m : Mem) (kind : BlockKind) (size align : Nat) : Mem :=
  { m with
    blocks := m.blocks.push
      { bytes := Array.replicate size .undef, align, kind, live := true,
        addr := m.newAddr kind size align }
    nextAddr := m.newNext kind size align }

/-- A new block of `size` undefined bytes. Its id is new (`m.blocks.size`). Its address is new
(the next free address, rounded up to `align`), unless the policy reuses one
(`Mem.reuseAddr?`): then `nextAddr` stays. -/
def alloc (kind : BlockKind) (size align : Nat) : MemM Ptr := do
  let m ← get
  set (m.afterAlloc kind size align)
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
that is not valid (`@memcpy` still checks its counts). For more items, the access is checked
before the bytes are made. -/

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

/-- `@memmove`: copy `n` items of `size` bytes from `src` to `dst`. All bytes are read before the
first write, so an overlap copies the old bytes. -/
def memmove (size dstAlign srcAlign : Nat) (dst src : Ptr) (n : BitVec 64) : MemM Unit := do
  if n.toNat = 0 ∨ size = 0 then return
  let _ ← (← get).access dst (n.toNat * size) dstAlign
  let bs ← loadBytes src (n.toNat * size) srcAlign
  storeBytes dst dstAlign bs

/-- The `len` bytes at `p` and at `q` overlap: the same block (or both raw addresses) and
intersecting offset ranges. -/
def Ptr.overlaps (p q : Ptr) (len : Nat) : Bool :=
  len ≠ 0 && p.block == q.block && p.off < q.off + len && q.off < p.off + len

/-- `@memcpy` (AIR `memcpy`): `@memmove` of `n` items, where `m` is the item count of `src` (`n`
if `src` has no length). Unequal counts and overlapping ranges are illegal behaviour that only
Sema's safety checks (`copyLenMismatch`, `memcpyAlias`) catch, so the model checks them itself:
`.illegal` (`docs/illegal-behavior.md`). With the checks the panic comes first. -/
def memcpy (size dstAlign srcAlign : Nat) (dst src : Ptr) (n m : BitVec 64) : MemM Unit :=
  if n ≠ m || dst.overlaps src (n.toNat * size) then throw .illegal
  else memmove size dstAlign srcAlign dst src n

/-- `slice_elem_val` in memory: an index at or past the length is illegal behaviour that only
Sema's bounds check (`outOfBounds`) catches, so the model checks it itself: `.illegal`. -/
def checkIndex (s : Slice) (i : BitVec 64) : MemM Unit :=
  if i.toNat < s.len.toNat then pure () else throw .illegal

/-- Slicing `[start..start + len]` of an operand with `srcLen` items: an end past the length is
illegal behaviour that only Sema's bounds check (`outOfBounds`) catches: `.illegal`. `extra` is
`1` for a sentinel slicing whose sentinel item must also be an item of the operand. -/
def checkSliceEnd (srcLen start len : BitVec 64) (extra : Nat) : MemM Unit :=
  if start.toNat + len.toNat + extra ≤ srcLen.toNat then pure () else throw .illegal

/-- `@fieldParentPtr` to a struct with no defined layout: the parent pointer `q` must address a
live, aligned object of the parent's `size` bytes. A field pointer that is not into such an
object is illegal behaviour that nothing checks: `.illegal`. -/
def checkParent (size align : Nat) (q : Ptr) : MemM Unit := do
  let _ ← (← get).access q size align

/-- `checkIndex` for a slice with a sentinel (`[:s]T`): its sentinel item, at the length, is an
item too (Sema reads it to check sentinel slicing). -/
def checkSentinelIndex (s : Slice) (i : BitVec 64) : MemM Unit :=
  if i.toNat ≤ s.len.toNat then pure () else throw .illegal

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

/-- The pointer to address `n`: inside or one past the block whose address range covers `n`, at
the matching offset, or `⟨none, n⟩` if no block covers it (`@ptrFromInt`). A dead block still
counts (its `addr` does not change on `free`), so the pointer this returns can still be a
dangling one; the existing liveness check in `Mem.access` catches a later access through it.
Round-trips with `ptrAddr`: `ptrFromAddr (← ptrAddr p) = p` for `p` inside or one past its
block's bytes.

With fresh addresses (the default), at most one block covers `n`. Under address reuse
(`AllocPolicy.reuseAddr`) a freed block and a later block can both cover it, and the integer does
not say which one it came from. Then the policy's `provenance` decides: `.strict` (the default)
throws `.unspecified`; the address-sensitive contract `.liveBlock` takes the live block
(`docs/address-reuse.md`). -/
def ptrFromAddr (n : Nat) : MemM Ptr := do
  let m ← get
  let hits := m.blocks.zipIdx.filterMap fun (blk, b) =>
    if blk.addr ≤ n ∧ n ≤ blk.addr + blk.bytes.size then some (b, blk) else none
  match hits.toList with
  | [] => pure ⟨none, n⟩
  | [(b, blk)] => pure ⟨some b, (n : Int) - (blk.addr : Int)⟩
  | _ =>
    match m.allocPolicy.provenance with
    | .strict => throw .unspecified
    | .liveBlock =>
      match hits.find? (·.2.live) with
      | some (b, blk) => pure ⟨some b, (n : Int) - (blk.addr : Int)⟩
      | none => throw .unspecified

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
