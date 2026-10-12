import ZigLean.Basic
import ZigLean.Env.Host

/-!
# Byte-level memory

A CompCert-style memory: a list of blocks, each an array of bytes. A pointer is a block and a
byte offset, so a pointer stored in memory keeps its block (`Byte.ptrFrag`). Blocks are never
removed: `free` marks a block dead, and every later access to it throws `.illegal`.

A function that uses memory (`docs/generated-code.md` §Memory) returns `Zig.MemM α`, and its
body runs in `Zig.MM σ ε`. A pure function keeps `Zig.Result α` and `Zig.M σ ε`.

Each block gets an address when it is made: a global at program start, a stack block at
function entry, a heap or allocator block at `alloc`. The address is chosen by the environment,
the placement oracle `Mem.place` (`docs/address-placement.md`, MM-1): a proposal is taken if it
satisfies what Zig guarantees and nothing more (`Mem.placeOk`: not 0, a multiple of the block's
alignment, inside the address space (`Placement.addrLimit`), disjoint from every live block; no
gap and no order). A block that the placement cannot fit inside the address space is never made
(`Mem.roomFor`, `alloc`). A generated
program-start memory takes the placement as a parameter (`mem0 σ`), so a theorem about it holds
for every placement. Block ids stay unique, and every lifetime check uses the block id, not the
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
  (`Byte.ofDefBits`, `ZigLean/Mem/Enc.lean`). A read that needs a bit outside `d` throws
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
  /-- An OS page mapping (`posix.mmap`, `ZigLean/Os/Mmap.lean`, premise OSM-01). The mapping's
  live bytes are the offsets from `lo` to the block's size: `munmap` of a page prefix moves `lo`
  up, of a page tail shrinks the bytes, of the whole mapping ends the block. An access below
  `lo` throws `.illegal` (`Mem.access`), as one past the size does. -/
  | mapped (lo : Nat)
  deriving DecidableEq, Repr

/-- The first live offset of a block: `lo` for an OS mapping (`.mapped lo`), 0 otherwise. -/
def BlockKind.mappedLo : BlockKind → Nat
  | .mapped lo => lo
  | _ => 0

@[simp] theorem BlockKind.mappedLo_mapped (lo : Nat) : (BlockKind.mapped lo).mappedLo = lo := rfl
@[simp] theorem BlockKind.mappedLo_stack : BlockKind.stack.mappedLo = 0 := rfl
@[simp] theorem BlockKind.mappedLo_heap : BlockKind.heap.mappedLo = 0 := rfl
@[simp] theorem BlockKind.mappedLo_global : BlockKind.global.mappedLo = 0 := rfl
@[simp] theorem BlockKind.mappedLo_constGlobal : BlockKind.constGlobal.mappedLo = 0 := rfl
@[simp] theorem BlockKind.mappedLo_owned (a : AllocId) : (BlockKind.owned a).mappedLo = 0 := rfl

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
globals and for a thread that has not started. `gated`: a deferred `Io.Group` task
(`Thread.forkGated`); it does not start while its group still records it (`Mem.isGated`,
`ZigLean/Conc/Sched.lean`). -/
structure ThreadRec where
  spawner : ThreadId
  joined : Bool
  tls : Array (BlockId × BlockId) := #[]
  gated : Bool := false
  /-- The join obligation ended without a happens-before edge to the owner: `pthread_detach`, or
  a Linux `clone` thread's exit (`Os.markExited`). `Mem.freeRaces` then does not exempt the
  thread's accesses. -/
  released : Bool := false
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
  /-- The thread of an atomic store or RMW (`none` for a plain write). Ghost: it only decides
  the owner check of a mutex unlock (`Thread.mutexOwnerCheck`, `ALoc.holder`). -/
  writer : Option ThreadId := none
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
the address (`ptrFromAddr`): a freed block and a later block at its address (address reuse,
`docs/address-reuse.md`), or one block's one-past-the-end address that starts the next block (two
blocks may be adjacent, `docs/address-placement.md`). -/
inductive ProvenanceMode where
  /-- The default: the integer does not say which block it came from, so the recovery gives no
  provenance (`⟨none, n⟩`: the address only, every access `.illegal`). A stale integer never
  gains the provenance of the block that reuses its address. -/
  | strict
  /-- The address-sensitive contract: the address recovers the provenance of the live block that
  covers it (live blocks never share an address). A program that declares it asserts that each
  integer it converts belongs to that block, also a stale one. -/
  | liveBlock
  deriving DecidableEq, Repr, Inhabited

/-- The OS page-mapping oracle (premise OSM-01, `ZigLean/Os/Mmap.lean`). Whether an `mmap` or a
growing `mremap` fails is the allocator failure decision (`Mem.allocDenied`, one attempt index
for every request); this picks only whether a growth that may move does move, from the attempt
index and the requested length in bytes. -/
structure OsPolicy where
  /-- A growth with `MREMAP.MAYMOVE` moves the mapping to a fresh address. -/
  mremapMoves : Nat → Nat → Bool := fun _ _ => false
  deriving Inhabited

/-- Selected allocator environment: a per-request cap, finite failure indices, an arbitrary
failure oracle over (attempt index, request bytes) and an optional live-heap budget.
The cap and finite list are special cases of the oracle (`AllocPolicy.asOracle` in
`ZigLean.Sep.Alloc`).
It is not a claim about a native allocator's available memory. Addresses are not part of it:
the placement oracle (`Mem.place`) chooses the address of every block. -/
structure AllocPolicy where
  maxBytes : Nat := unboundedAllocBytes
  failures : List Nat := []
  byteRemap : ByteRemapMode := .fail
  /-- Arbitrary permitted failure decisions: `fails i n` fails attempt `i` of `n` bytes. -/
  fails : Nat → Nat → Bool := fun _ _ => false
  /-- Total live-heap bytes allowed after the request; `none` is unbounded. -/
  budget : Option Nat := none
  /-- `@ptrFromInt` of an address that more than one block covers. -/
  provenance : ProvenanceMode := .strict
  /-- The move choice of the OS page-mapping model (`ZigLean/Os/Mmap.lean`). -/
  os : OsPolicy := {}
  deriving Inhabited

/-- The oracles are functions, so they are shown opaquely. -/
instance : Repr AllocPolicy where
  reprPrec p _ := f!"\{ maxBytes := {repr p.maxBytes}, failures := {repr p.failures}, " ++
    f!"byteRemap := {repr p.byteRemap}, fails := <oracle>, budget := {repr p.budget}, " ++
    f!"provenance := {repr p.provenance}, os := <oracle> }"

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

/-! ## `noalias` scopes (`ZigLean/Mem/Noalias.lean`, `docs/illegal-behavior.md`) -/

/-- One access in the log of a `noalias` scope: its bytes, whether it writes, and its root, the
`noalias` parameter that the pointer of the access is based on (`none`: none of them). -/
structure NaEntry where
  block : BlockId
  off : Nat
  len : Nat
  write : Bool
  root : Option Nat
  deriving Repr, Inhabited

/-- One running call of a function with `noalias` parameters, on thread `tid`. `seen`: the
footprint entries before it are in `log` (or before the call); the ones after it are the
accesses of the instruction that the next `Zig.naMark` follows. -/
structure NaScope where
  tid : ThreadId
  seen : Nat
  log : Array NaEntry := #[]
  deriving Repr, Inhabited

/-- Address placement (MM-1, `docs/address-placement.md`): the environment's choice of the
address of each block, of every kind (global, stack, heap, allocator). `propose b` is the address
of block `b`; the model takes it if it is valid (`Mem.placeOk`), else the block gets the next
free address after every block (`Mem.top`). The oracle is an arbitrary function of the block id,
and a run is deterministic given it, so quantifying over it covers every address assignment
that keeps live blocks apart: every native layout, with or without address reuse.

`addrLimit` is the end of the user address space (O-H, premise SEM-07): no block ends above it,
of any kind. A theorem for every placement holds for every limit up to `2 ^ 63`, which covers
every modelled 64-bit target (user space in the lower half). The default is `2 ^ 47`, the smaller
of the two OS targets' limits (`Os.Target.addrLimit`). -/
structure Placement where
  propose : BlockId → Option Nat
  /-- The end of the user address space (module doc). -/
  addrLimit : Nat := 2 ^ 47
  addrLimit_le : addrLimit ≤ 2 ^ 63 := by decide
  /-- The start of thread `t`'s stack reserve (`Mem.withStack`, MM-18), if the placement picks
  one; an invalid proposal falls back to the first fit. For a native run it is address space the
  run never maps (premise STK-02). -/
  reserve : ThreadId → Option Nat := fun _ => none

/-- The placement that proposes nothing: every block at the next free address after every other
block, from 4096, with a 1-byte gap. Only for running a program (`#eval`, the differential
harness); a theorem about a generated program holds for every placement. -/
def Placement.fresh : Placement := { propose := fun _ => none }

instance : Inhabited Placement := ⟨.fresh⟩

/-- The oracle is a function, so it is shown opaquely. -/
instance : Repr Placement := ⟨fun _ _ => "<placement>"⟩

/-- The kernel's and libc's per-process state that the trusted OS thread primitives keep
(`ZigLean/Os/`, `docs/os-threads.md`). Only those models read or write it. -/
structure OsState where
  /-- The threads with a pending interrupt (`tgkill`/`pthread_kill` of `SIG.IO`, premise OSG-01). -/
  interrupts : Array ThreadId := #[]
  /-- The number of clock reads so far: the index of the next one into the clock oracle
  (premise OSK-01). -/
  clockReads : Nat := 0
  /-- Each thread's libc `errno` cell (macOS `__error()`), made at its first use. -/
  errno : Array (ThreadId × BlockId) := #[]
  /-- The threads that `pthread_detach` released: they stay signalable while they run. -/
  detached : Array ThreadId := #[]
  deriving Repr, Inhabited

/-- One entry of a thread's stack accounting (MM-18, `docs/architecture-audit/memory-model.md`):
a stack block (`some b`, live while the block is) or the frame charge of a recursive call
(`none`, live until `leaveFrame` closes it). -/
structure StackEntry where
  block : Option BlockId
  /-- The depth at its push: the end of the entry below it. -/
  base : Nat
  charge : Nat
  closed : Bool := false
  deriving Repr, Inhabited, DecidableEq

/-- A thread's stack (MM-18). With a budget `S` the thread owns the reserve `[base, base + S)`,
which no other block meets, and its stack blocks and frames are charged LIFO: `entries` in push
order, popped lazily (`StackState.held`). Without a budget (`none`, the default) there is no
accounting: a stack block is placed like any other block. -/
structure StackState where
  budget : Option Nat := none
  base : Nat := 0
  entries : Array StackEntry := #[]
  deriving Repr, Inhabited

structure Mem where
  blocks : Array Block := #[]
  /-- The address of every new block (`Mem.newAddr`). -/
  place : Placement := .fresh
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
  a futex, and the address. A wake picks among them (`Thread.wakeSet`): the order is not a
  wake order. -/
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
  /-- `stacks[t]`: thread `t`'s stack budget, reserve and LIFO accounting (MM-5, MM-18;
  `Mem.stackOf`). Empty (the default, and every generated `mem0`): no thread has a budget, and a
  statement about such a memory assumes that the native stack holds every call chain it reaches
  (premise STK-01, `docs/premises.md`). `Mem.withStack` gives the main thread one. -/
  stacks : Array StackState := #[]
  /-- The running calls of functions with `noalias` parameters, innermost last
  (`ZigLean/Mem/Noalias.lean`). Empty in every program without one. -/
  noalias : Array NaScope := #[]
  /-- The explicit oracle of arbitrary words (`arbitraryWord`, `--allocator-model translated`,
  `docs/allocator-model.md`): query `k` (from 0, in execution order) returns `arbitrary[k]`,
  `0` past the end. `@returnAddress()` and an `undefined` pointer operand read it. Every finite
  run makes finitely many queries, so a theorem about every initial `Mem` holds for every
  sequence of values; nothing ties a value to a real code address. -/
  arbitrary : Array (BitVec 64) := #[]
  /-- The number of `arbitraryWord` queries so far. -/
  arbitraryNext : Nat := 0
  /-- The state of the trusted OS thread primitives (`ZigLean/Os/`). -/
  os : OsState := {}
  deriving Repr, Inhabited

/-- Thread `t` is a deferred task (`ThreadRec.gated`) that its group still records: no `await` or
`cancel` of the group has taken it (`Thread.groupTake`), so it has not started. -/
def Mem.isGated (m : Mem) (t : ThreadId) : Bool :=
  (m.threads[t]?.map (·.gated)).getD false && m.groups.any (·.2 == t)

/-- The state of a function that uses memory. -/
abbrev MemM (α : Type) := StateT Mem Result α

/-- The body monad of a function that uses memory: its locals over `MemM`. -/
abbrev MM (σ α : Type) := StateT σ MemM α

/-- The next value of the explicit oracle `Mem.arbitrary`. No memory access. -/
def arbitraryWord : MemM (BitVec 64) := do
  let m ← get
  set { m with arbitraryNext := m.arbitraryNext + 1 }
  pure (m.arbitrary.getD m.arbitraryNext 0)

/-- `@returnAddress()`: an arbitrary `usize` (`arbitraryWord`). Allocators only pass it along
as `ret_addr`. -/
def returnAddress : MemM (BitVec 64) := arbitraryWord

/-- An `undefined` pointer operand (`--allocator-model translated`, e.g. the `ptr` of
`std.heap.page_allocator`): a pointer without a block at an arbitrary address
(`arbitraryWord`), so every access through it throws `.illegal`. -/
def undefPtr : MemM Ptr := do
  pure ⟨none, (← arbitraryWord).toNat⟩

/-- `n` rounded up to a multiple of `a` (`a = 0`: `n`). -/
def alignUp (n a : Nat) : Nat := if a = 0 then n else (n + a - 1) / a * a

/-- The block and the offset of an access of `n` bytes at `p` that needs alignment `align`.
Throws `.illegal` if the block is dead, the bytes are not all in the block (for an OS mapping:
not all at or above its first live offset, `BlockKind.mappedLo`), or the address is not a
multiple of `align`. -/
def Mem.access (m : Mem) (p : Ptr) (n align : Nat) : Result (BlockId × Block × Nat) :=
  match p.block with
  | none => throw .illegal
  | some b =>
    match m.blocks[b]? with
    | none => throw .illegal
    | some blk =>
      if blk.live ∧ 0 ≤ p.off ∧ p.off + n ≤ blk.bytes.size ∧ (blk.addr + p.off.toNat) % align = 0 ∧
          blk.kind.mappedLo ≤ p.off.toNat
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

/-- Only the main thread can run: it is the current thread and every spawned thread has been
joined. Then no recorded access is concurrent with the current one: the main thread's own
accesses happened before, and a join merged each joined thread's clock (which covers that
thread's accesses and, through its own joins, its children's) into the joiner's. -/
def Mem.solo (m : Mem) : Bool := m.current == 0 && m.threads.all (·.joined)

/-- The race check of `recordAccess`: `raceAt` over the footprint, skipped when `m.solo`. In
every memory that a run from `Mem.ofGlobals` reaches, `raceAt` is `none` when `m.solo`
(`raceCheck_eq_raceAt` states it for single-thread memories), so the skip changes no outcome;
it keeps a single-thread run linear instead of quadratic in its number of accesses (MM-14). -/
def raceCheck (m : Mem) (clock : VClock) (block : BlockId) (off len : Nat) (kind : AccessKind) :
    Option Error :=
  if m.solo then none else raceAt m.footprint clock block off len kind

/-- Record one access at `block`/`off`/`len` by the current thread (`ZigLean/Mem/Thread.lean`),
checking it against every earlier overlapping access from a concurrent thread (`racePair`, via
`raceCheck`). Throws the race's error before recording anything. -/
def recordAccess (block : BlockId) (off len : Nat) (kind : AccessKind) : MemM Unit := do
  let m ← get
  let t := m.current
  let clock := VClock.bump (m.clocks[t]!) t
  match raceCheck m clock block off len kind with
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

/-- `blk` does not constrain a range `[A, A + n)`: it is dead, one of the two ranges is empty, or
they are disjoint. Zig guarantees disjoint storage for live objects, nothing else (no gap, no
order, no separation for a zero-size object). -/
def Block.clearOf (blk : Block) (A n : Nat) : Bool :=
  !blk.live || n == 0 || blk.bytes.size == 0 ||
    decide (A + n ≤ blk.addr) || decide (blk.addr + blk.bytes.size ≤ A)

/-- No live block's address range meets `[A, A + n)` (`Block.clearOf`). -/
def Mem.addrFree (m : Mem) (A n : Nat) : Bool :=
  m.blocks.all (·.clearOf A n)

/-- The reserve of `s` (`[base, base + S)` with a budget `S`, nothing without one) does not meet
`[A, A + n)`. -/
def StackState.reserveClear (s : StackState) (A n : Nat) : Bool :=
  match s.budget with
  | none => true
  | some S => n == 0 || S == 0 || decide (A + n ≤ s.base) || decide (s.base + S ≤ A)

/-- No thread's stack reserve meets `[A, A + n)` (MM-18). -/
def Mem.reservesFree (m : Mem) (A n : Nat) : Bool :=
  m.stacks.all (·.reserveClear A n)

/-- `A` is an address for a new block of `size` bytes with alignment `align` that the live blocks
allow: not 0, a multiple of the alignment, the block inside the address space
(`Placement.addrLimit`), and disjoint from every live block (`Mem.addrFree`). -/
def Mem.fitOk (m : Mem) (A size align : Nat) : Bool :=
  decide (0 < A) && decide (A % align = 0) && decide (A + size ≤ m.place.addrLimit) &&
    m.addrFree A size

/-- `A` is a valid address for a new block of `size` bytes with alignment `align`: exactly what
Zig guarantees about the address of an object (`Mem.fitOk`), outside every thread's stack reserve
(`Mem.reservesFree`, MM-18: a native run never maps a reserve, premise STK-02). It may be the
address of a dead block (reuse) and it may be adjacent to a live one. -/
def Mem.placeOk (m : Mem) (A size align : Nat) : Bool :=
  m.fitOk A size align && m.reservesFree A size

/-- The placement's address for the next block, if it is valid (`Mem.placeOk`). -/
def Mem.placed? (m : Mem) (size align : Nat) : Option Nat :=
  match m.place.propose m.blocks.size with
  | some A => if m.placeOk A size align then some A else none
  | none => none

/-- One past the end of a thread's stack reserve (0 without a budget). -/
def StackState.reserveEnd (s : StackState) : Nat :=
  match s.budget with
  | some S => s.base + S + 1
  | none => 0

/-- One past the end of every block, dead or live, and of every stack reserve, plus a gap byte;
at least 4096. The fallback address of a new block (`Mem.newAddr`) starts here, so it is clear of
every block and every reserve. -/
def Mem.top (m : Mem) : Nat :=
  m.stacks.foldl (fun t s => Nat.max t s.reserveEnd)
    (m.blocks.foldl (fun t blk => Nat.max t (blk.addr + blk.bytes.size + 1)) 4096)

/-- The address of a new block: the placement's (`Mem.placed?`), or `Mem.top` rounded up to
`align`. -/
def Mem.newAddr (m : Mem) (size align : Nat) : Nat :=
  match m.placed? size align with
  | some A => A
  | none => alignUp m.top align

/-- The new block fits inside the address space (`Placement.addrLimit`): always for a placed
address (`Mem.placeOk`), and for the fallback after `Mem.top` while that ends inside it. -/
def Mem.roomFor (m : Mem) (size align : Nat) : Bool :=
  decide (m.newAddr size align + size ≤ m.place.addrLimit)

/-! ## Stack regions (MM-18, `docs/architecture-audit/memory-model.md`)

A thread with a stack budget `S` owns the reserve `[base, base + S)`, which every other placement
avoids (`Mem.placeOk`, `Mem.top`, `Mem.growFree`, `Mem.mappingRoom`). Its stack blocks
(`alloc .stack`) and the frames of its recursive calls (`enterFrame`) are charged LIFO: a new entry
charges `stackCharge size align` (`frameBase` for a frame) and overflows when the depth would pass
`S`. The addresses stay the placement's (native code reorders and shares stack slots, MM-18 E1,
E1', E2); a block that the placement does not place goes to the LIFO fallback inside the reserve,
just below the held entries. An entry pops when it and every entry above it are dead (lazily,
`StackState.held`), so a `free` of the top block gives its charge back and an out-of-order `free`
gives it back late, never early. -/

/-- Thread `t`'s stack state (none recorded: no budget). -/
def Mem.stackOf (m : Mem) (t : ThreadId) : StackState := m.stacks.getD t default

/-- `ss` with thread `t`'s stack state `s` (padded with states without a budget). -/
def setStackAt (ss : Array StackState) (t : ThreadId) (s : StackState) : Array StackState :=
  if t < ss.size then ss.set! t s else (ss ++ Array.replicate (t - ss.size) default).push s

/-- The entry is live: its block is live, or its frame is not closed. -/
def StackEntry.liveIn (blocks : Array Block) (e : StackEntry) : Bool :=
  match e.block with
  | some b => (blocks[b]?.map (·.live)).getD false
  | none => !e.closed

/-- The entries up to the topmost live one; the dead ones above it are popped. -/
def StackState.held (s : StackState) (blocks : Array Block) : Array StackEntry :=
  s.entries.popWhile (!·.liveIn blocks)

/-- The charge of entries `h`: the end of the topmost one (each entry starts where the one below
it ends, `Mem.pushEntry`). -/
def stackEnd (h : Array StackEntry) : Nat :=
  match h.back? with
  | some e => e.base + e.charge
  | none => 0

/-- The charge of the held entries. -/
def StackState.depth (s : StackState) (blocks : Array Block) : Nat := stackEnd (s.held blocks)

/-- Thread `t`'s stack depth: the charge of its held entries. -/
def Mem.stackDepth (m : Mem) (t : ThreadId) : Nat := (m.stackOf t).depth m.blocks

/-- The charge of a stack block: its size plus its alignment (at least 1), which covers the
padding of the LIFO fallback. Not a bound on the native frame (premise STK-01). -/
def stackCharge (size align : Nat) : Nat := size + Nat.max align 1

/-- `n` rounded down to a multiple of `a` (`a > 0`). -/
def alignDown (n a : Nat) : Nat := n / a * a

/-- The current thread's stack budget, for a block of kind `kind`: `none` unless it is a stack
block of a thread with a budget. -/
def Mem.stackBudget? (m : Mem) : BlockKind → Option Nat
  | .stack => (m.stackOf m.current).budget
  | _ => none

/-- The LIFO fallback of a stack block in the current thread's reserve: the highest aligned
address below the held entries' charge from the reserve's end. -/
def Mem.stackFallback (m : Mem) (S size align : Nat) : Nat :=
  alignDown ((m.stackOf m.current).base + S - m.stackDepth m.current - size) (Nat.max align 1)

/-- The address of a new block of kind `kind`: the placement's (`Mem.placed?`); else a stack
block of a thread with a budget gets the LIFO fallback in its reserve and every other block
`Mem.top` rounded up (`Mem.newAddr`). -/
def Mem.allocAddr (m : Mem) (kind : BlockKind) (size align : Nat) : Nat :=
  match m.stackBudget? kind with
  | none => m.newAddr size align
  | some S => (m.placed? size align).getD (m.stackFallback S size align)

/-- `alloc` can make the block: room in the address space (`Mem.roomFor`); for a stack block of a
thread with a budget `S`, its charge fits (depth plus charge at most `S`) and its address is
valid (`Mem.fitOk`; the fallback in the reserve always is in a memory that a run reaches). -/
def Mem.allocOk (m : Mem) (kind : BlockKind) (size align : Nat) : Bool :=
  match m.stackBudget? kind with
  | none => m.roomFor size align
  | some S => decide (m.stackDepth m.current + stackCharge size align ≤ S) &&
      m.fitOk (m.allocAddr kind size align) size (Nat.max align 1)

/-- The stacks after pushing an entry for `block` with charge `c` on the current thread's held
entries, at their depth. -/
def Mem.pushEntry (m : Mem) (block : Option BlockId) (c : Nat) : Array StackState :=
  let s := m.stackOf m.current
  let h := s.held m.blocks
  setStackAt m.stacks m.current { s with entries := h.push { block, base := stackEnd h, charge := c } }

/-- The stacks after `alloc`: a stack block of a thread with a budget pushes its entry. -/
def Mem.stacksAfterAlloc (m : Mem) (kind : BlockKind) (size align : Nat) : Array StackState :=
  match m.stackBudget? kind with
  | none => m.stacks
  | some _ => m.pushEntry (some m.blocks.size) (stackCharge size align)

/-- The memory after `alloc`: one more block, `m.blocks.size`, of `size` undefined bytes, at
`Mem.allocAddr`, and its stack entry (`Mem.stacksAfterAlloc`). -/
def Mem.afterAlloc (m : Mem) (kind : BlockKind) (size align : Nat) : Mem :=
  { m with
    blocks := m.blocks.push
      { bytes := Array.replicate size .undef, align, kind, live := true,
        addr := m.allocAddr kind size align }
    stacks := m.stacksAfterAlloc kind size align }

/-- A new block of `size` undefined bytes. Its id is new (`m.blocks.size`); its address is the
placement's (`Mem.allocAddr`). The block is never placed above `Placement.addrLimit` (O-H): without
room (`Mem.allocOk`) the run throws `.stackOverflow`, the outcome of an exhausted stack budget
(MM-5, MM-18, premise STK-01). `alloc` makes the blocks that have no allocator of their own: stack
locals (`allocStack`), thread-local instances and the runtime's cells; every allocator path
checks room first and fails as out of memory (`rawAlloc` returns null, `mmap` fails with
`ENOMEM`). -/
def alloc (kind : BlockKind) (size align : Nat) : MemM Ptr := do
  let m ← get
  if m.allocOk kind size align then
    set (m.afterAlloc kind size align)
    pure ⟨some m.blocks.size, 0⟩
  else throw .stackOverflow

/-- The end of block `b`'s life (`n` bytes; a frame exit, `rawFree`) races with an earlier access
`e` to its bytes by another thread unless `e` happened before it: by `e`'s clock, by the clock of
`e`'s thread now (which is above each access of that thread), or because `e`'s thread is a child
of the current thread that it joined (the join is after each access of the child; a detached or
exited child, `ThreadRec.released`, gives no such edge). The end of a
block is a write of all its bytes for the race check (C11: the bytes are reused). -/
def Mem.freeRaces (m : Mem) (b : BlockId) (n : Nat) : Bool :=
  let c := VClock.bump (m.clocks[m.current]!) m.current
  m.footprint.any fun e => e.block == b && 0 < e.off + e.len && e.off < n && e.tid != m.current &&
    !VClock.le e.clock c && !VClock.le (m.clocks[e.tid]!) c &&
    !(m.threads[e.tid]?.any fun r => r.spawner == m.current && r.joined && !r.released)

/-- Free the block that `p` points to the start of. A dead block, an inner pointer or a `const`
global (read-only static storage, which native code cannot free) throws `.illegal`; so does an
end of the block that races with an access by another thread (`Mem.freeRaces`). It records
nothing: a later access to the dead block is `.illegal`. So a `const` global, once live, keeps
its bytes and stays live in every later memory (`docs/sep-full-state.md` §Const globals). -/
def free (p : Ptr) : MemM Unit := do
  let m ← get
  match p.block with
  | none => throw .illegal
  | some b =>
    match m.blocks[b]? with
    | some blk =>
      if blk.live ∧ p.off = 0 ∧ blk.kind ≠ .constGlobal then
        if m.freeRaces b blk.bytes.size then throw .illegal
        else set { m with blocks := m.blocks.set! b { blk with live := false } }
      else throw .illegal
    | none => throw .illegal

/-- The stack block of a local whose address escapes: made at function entry. -/
@[inline] def allocStack (size align : Nat) : MemM Ptr := alloc .stack size align

/-! ## Frames of recursive calls (MM-5, MM-18)

A function of a recursive call group that uses memory charges its frame when it is entered
(`enterFrame`) and releases it when it returns (`leaveFrame`). The frame charge is `frameBase`;
its escaping locals are charged by their own stack blocks (`alloc .stack`). AIR has no frame
size: native frames also hold spill slots, saved registers and locals that the model keeps as
values, and inlining or tail calls can merge frames. So the charge ties a model overflow to the
depth of the recursion; it is not a bound on the native frame (`docs/premises.md` STK-01). -/

/-- The fixed part of every charged frame: a return address and a saved frame pointer. -/
def frameBase : Nat := 16

/-- Charge a frame of `frameBase` bytes to the current thread's stack: `.stackOverflow` if the
depth would pass its budget. Without a budget nothing is charged. -/
def enterFrame : MemM Unit := do
  let m ← get
  match (m.stackOf m.current).budget with
  | none => pure ()
  | some S =>
    if S < m.stackDepth m.current + frameBase then throw .stackOverflow
    else set { m with stacks := m.pushEntry none frameBase }

/-- `s` with its topmost open frame entry below index `i` closed (a backward scan). -/
def StackState.closeFrame (s : StackState) (i : Nat := s.entries.size) : StackState :=
  match i with
  | 0 => s
  | i + 1 =>
    match s.entries[i]? with
    | some e =>
      if e.block.isNone && !e.closed then { s with entries := s.entries.set! i { e with closed := true } }
      else s.closeFrame i
    | none => s

/-- Release the frame that `enterFrame` charged: close the current thread's topmost open frame
entry (it pops with the dead entries above it). -/
def leaveFrame : MemM Unit :=
  modify fun m =>
    match (m.stackOf m.current).budget with
    | none => m
    | some _ => { m with stacks := setStackAt m.stacks m.current (m.stackOf m.current).closeFrame }

/-! ## Typed access -/

/-- The memory encoding of a Lean type: its size and alignment in bytes (the Zig ABI values),
and the bytes of a value. `decode` throws `.unspecified` if a byte that the value uses is
undefined; padding bytes are ignored. -/
class Enc (α : Type) where
  size : Nat
  align : Nat
  encode : α → Array Byte
  decode : Array Byte → Result α

/-- The address of `p` over the blocks `blocks` (`ptrAddr`), if its block exists. -/
def addrIn (blocks : Array Block) (p : Ptr) : Option Int :=
  match p.block with
  | none => some p.off
  | some b => (blocks[b]?).map fun blk => blk.addr + p.off

/-- `bs` with every pointer byte replaced by the byte of its pointer's address
(little-endian, two's complement in 64 bits): the bytes as an integer read sees them (MM-11). A
pointer byte whose block does not exist stays. -/
def exposeBytes (blocks : Array Block) (bs : Array Byte) : Array Byte :=
  bs.map fun
    | .ptrFrag q i =>
      match addrIn blocks q with
      | some a => .int (BitVec.ofNat 8 ((BitVec.ofInt 64 a).toNat >>> (8 * i.val)))
      | none => .ptrFrag q i
    | b => b

/-- The byte is a pointer byte. -/
def Byte.isPtrFrag : Byte → Bool
  | .ptrFrag .. => true
  | _ => false

/-- The decode of a load (MM-11, PNVI-ae style exposure): `Enc.decode bs`, except that a decode
that is `.unspecified` and meets pointer bytes is retried with the pointer bytes read as their
addresses (`exposeBytes`, over the memory's `blocks`). So the bytes of a pointer read as an
integer (`asBytes(&p)`, a `*usize` cast of `&p`) give its address, as in Zig. A value that mixes
a pointer and integer bytes holding a pointer then decodes its pointer from the address, without
a block. Integer bytes read as a pointer give a pointer without a block (`Enc Ptr`). -/
def decodeLoad {α : Type} [Enc α] (blocks : Array Block) (bs : Array Byte) : Result α :=
  ExceptT.mk <|
    match (Enc.decode bs : Result α).run with
    | some (.error .unspecified) =>
      if bs.any Byte.isPtrFrag then (Enc.decode (exposeBytes blocks bs) : Result α).run
      else some (.error .unspecified)
    | r => r

/-- `load`/`store` take the alignment of the pointer type (`*align(N) T`), which can differ from
the type's own alignment. -/
def load (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM α := do
  let bs ← loadBytes p (Enc.size α) align
  decodeLoad (← get).blocks bs

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

/-- Item `i` of an operand with `len` items: a slice's length, or the count of the array or
vector that a pointer points to (`slice_elem_val`, `slice_elem_ptr`, `ptr_elem_val`,
`ptr_elem_ptr`). An index at or past the length is illegal behaviour that only Sema's bounds
check (`outOfBounds`) catches, so the model checks it itself: `.illegal`. Forming the pointer
`&s[i]` is already illegal; the item does not need to be read. A many-item pointer has no
length and no check. -/
def checkIndex {n : Nat} (len i : BitVec n) : MemM Unit :=
  if i.toNat < len.toNat then pure () else throw .illegal

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

/-- `checkIndex` for an operand with a sentinel (`[:s]T`, `*[n:s]T`): its sentinel item, at the
length, is an item too (Sema's bounds check is `i ≤ len`). -/
def checkSentinelIndex {n : Nat} (len i : BitVec n) : MemM Unit :=
  if i.toNat ≤ len.toNat then pure () else throw .illegal

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
block's bytes, if no other block covers the address.

More than one block covers `n` when a freed block and a later block share addresses (reuse), or
when `n` is one past the end of a block and the start of an adjacent one: the integer does not
say which one it came from. Then the policy's `provenance` decides: `.strict` (the default)
gives no provenance; the address-sensitive contract `.liveBlock` takes the live block that
contains `n`, else a live block that ends at `n`, and gives no provenance if none of the
covering blocks is live (`docs/address-reuse.md`).

**No provenance** is `⟨none, n⟩`, as when no block covers `n`: its address is `n` (`ptrAddr`, so
`@intFromPtr` round-trips and `==` compares addresses), and every load, store, atomic op, `free`
or `munmap` through it is `.illegal` (`Mem.access` needs a block). This is a conservative
over-approximation: native code may dereference the address; the model claims nothing about such
an access. A program that only passes the address on (`std.heap.PageAllocator`'s `mmap` hint) is
unaffected. -/
def ptrFromAddr (n : Nat) : MemM Ptr := do
  let m ← get
  let hits := m.blocks.zipIdx.filterMap fun (blk, b) =>
    if blk.addr ≤ n ∧ n ≤ blk.addr + blk.bytes.size then some (b, blk) else none
  match hits.toList with
  | [] => pure ⟨none, n⟩
  | [(b, blk)] => pure ⟨some b, (n : Int) - (blk.addr : Int)⟩
  | _ =>
    match m.allocPolicy.provenance with
    | .strict => pure ⟨none, n⟩
    | .liveBlock =>
      match (hits.find? fun (_, blk) => blk.live ∧ n < blk.addr + blk.bytes.size) <|>
          hits.find? (·.2.live) with
      | some (b, blk) => pure ⟨some b, (n : Int) - (blk.addr : Int)⟩
      | none => pure ⟨none, n⟩

/-- `<`, `<=`, `>`, `>=` on pointers compare the addresses. The order of two blocks is the
placement's (`Mem.place`): nothing fixes it. -/
def ptrLt (a b : Ptr) : MemM Bool := do pure (decide ((← ptrAddr a) < (← ptrAddr b)))
def ptrLe (a b : Ptr) : MemM Bool := do pure (decide ((← ptrAddr a) ≤ (← ptrAddr b)))

/-- `==` and `!=` on pointers of every kind compare the addresses (MM-4), as LLVM's `icmp` does:
two pointers with different provenance but the same address are equal. Block identity is only
for liveness and provenance checks. -/
def ptrEqAddr (p q : Ptr) : MemM Bool := do
  pure (decide ((← ptrAddr p) = (← ptrAddr q)))

/-- `==` on optional pointers `?*T`: `null` is address 0, so two nulls are equal, null and a
pointer are not, and two pointers compare by address (`ptrEqAddr`). -/
def optPtrEqAddr : Option Ptr → Option Ptr → MemM Bool
  | none, none => pure true
  | some p, some q => ptrEqAddr p q
  | _, _ => pure false

/-! ## Pointer formation -/

/-- `p` is in bounds of its block in `m`: a byte of it or one past its end. The block may be
dead (LLVM: being in bounds of a deallocated object is enough). A pointer without a block is in
bounds of nothing. -/
def Mem.inBounds (m : Mem) (p : Ptr) : Bool :=
  match p.block with
  | none => false
  | some b =>
    match m.blocks[b]? with
    | none => false
    | some blk => decide (0 ≤ p.off ∧ p.off ≤ blk.bytes.size)

/-- A derived pointer: `project p`, an offset of `p` in its block (`struct_field_ptr`,
`ptr_add`, `ptr_sub`, `ptr_elem_ptr`, `slice_elem_ptr`, `@fieldParentPtr`, a slice's length
field, an error union's payload). Zig's LLVM backend (0.14.1, 0.15.2, 0.16.0) lowers all but
`@fieldParentPtr` to `getelementptr inbounds`, which is poison unless the base and the result
are in bounds of the base's allocation (`Mem.inBounds`, one past the end included), and to no
instruction for a constant offset 0. `@fieldParentPtr` (`ptrtoint`/`sub nuw`/`inttoptr`) is
illegal behaviour unless its operand is that field of a parent; the same rule rejects the
out-of-allocation part of that, not a wrong field of an in-bounds parent. So the same pointer is always allowed, also without a block (address zero, a
`@ptrFromInt` address); any other result throws `.illegal` unless both lie in `[0, size]` of
`p`'s block (`docs/architecture-audit/memory-model.md`, MM-3). The address is not observed. -/
def ptrProject (p : Ptr) (project : Ptr → Ptr) : MemM Ptr := fun m =>
  let q := project p
  if q = p ∨ (q.block = p.block ∧ m.inBounds p ∧ m.inBounds q) then pure (q, m)
  else throw .illegal

/-! ## Globals -/

/-- First fit from `A`: while `[A, A + size)` meets a live block, move `A` past that block
(rounded up to `align`), at most `fuel` times. -/
def Mem.fitFrom (m : Mem) (size align : Nat) : Nat → Nat → Nat
  | 0, A => A
  | fuel + 1, A =>
    match m.blocks.find? (fun blk => !blk.clearOf A size) with
    | none => A
    | some blk => m.fitFrom size align fuel (alignUp (blk.addr + blk.bytes.size) align)

/-- The lowest aligned address from 4096 up that the first-fit walk finds clear of every live
block (`Mem.fitFrom`). One step per block suffices (`Mem.firstFit_spec`). -/
def Mem.firstFit (m : Mem) (size align : Nat) : Nat :=
  m.fitFrom size align (m.blocks.size + 1) (alignUp 4096 align)

/-- The address of a global at program start: the placement's (`Mem.newAddr`) while it fits in
the address space (`Mem.roomFor`), else the first fit (`Mem.firstFit`). The first fit packs the
globals into the gaps the placement left, so the globals of every program whose globals fit
(`Mem.GlobalsFit`) end below `2 ^ 63` under every placement (`Mem.ofGlobals_liveBounded`). -/
def Mem.globalPlace (m : Mem) (size align : Nat) : Nat :=
  if m.roomFor size align then m.newAddr size align else m.firstFit size align

/-- The globals fit in the address space with room to spare: `4096 + (n + 1) * T ≤ 2 ^ 63`, `T`
the sum of their sizes and alignments. The translator rejects a program whose globals do not. -/
def Mem.GlobalsFit (gs : List (Array Byte × Nat × BlockKind)) : Prop :=
  4096 + (gs.length + 1) * (gs.map fun g => g.1.size + g.2.1).sum ≤ 2 ^ 63

instance (gs : List (Array Byte × Nat × BlockKind)) : Decidable (Mem.GlobalsFit gs) := by
  unfold Mem.GlobalsFit; infer_instance

/-- `m` with one more global block, `m.blocks.size`: `bytes`, at `Mem.globalPlace`. `kind`:
`.global` for a `var`, `.constGlobal` for anything else. -/
def Mem.addGlobal (m : Mem) (bytes : Array Byte) (align : Nat) (kind : BlockKind) : Mem :=
  { m with
    blocks := m.blocks.push
      { bytes, align, kind, live := true, addr := m.globalPlace bytes.size align } }

/-- The memory at program start under the placement `σ`: block `k` is global `k`, with its
initial bytes, alignment and kind, at the address that `σ` gives it. -/
def Mem.ofGlobals (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) : Mem :=
  gs.foldl (fun m (bs, a, k) => m.addGlobal bs a k) { place := σ }

/-- The start of a stack reserve of `S` bytes for thread `t` (MM-18): the placement's
(`Placement.reserve`) if it is a valid place for it (`Mem.placeOk`, 16-aligned), else the first
fit (`Mem.firstFit`) if that is valid; none if no place is found. -/
-- The first fit walks past live blocks only; a fit that meets another thread's reserve is
-- rejected (fail closed: no budget). Child reserves (MM-18 step 5) need a walk past reserves too.
def Mem.reserveAt? (m : Mem) (t : ThreadId) (S : Nat) : Option Nat :=
  match m.place.reserve t with
  | some A => if m.placeOk A S 16 then some A else fit
  | none => fit
where
  fit := let A := m.firstFit S 16; if m.placeOk A S 16 then some A else none

/-- `m` where the main thread has the stack budget `S` (MM-18): its reserve is placed
(`Mem.reserveAt?`) and its stack starts empty. Without a place for the reserve, `m` (no budget). -/
def Mem.withStack (m : Mem) (S : Nat) : Mem :=
  match m.reserveAt? 0 S with
  | some base => { m with stacks := setStackAt m.stacks 0 { budget := some S, base } }
  | none => m

/-- A block of external storage (L12, `docs/generated-code.md` §Globals): static storage that
another object defines, which the initial value of a pointer-bearing `extern` global can point
into. A generated `mem0` adds these blocks after the program's globals, in order, so block
`gs.length + i` is `ext.storage[i]`. It is never freed; a `const` one is read-only. -/
structure ExternBlock where
  bytes : Array Byte
  align : Nat
  writable : Bool

/-- The global block of `b`. -/
def ExternBlock.global (b : ExternBlock) : Array Byte × Nat × BlockKind :=
  (b.bytes, b.align, if b.writable then .global else .constGlobal)

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
