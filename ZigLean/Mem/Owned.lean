import ZigLean.Mem.Alloc

/-!
# Allocators with an identity (M01)

`ZigLean/Mem/Alloc.lean` models one allocator, the model's `std.mem.Allocator`: its blocks
have kind `.heap`. This file adds allocators with an identity, `std.heap.ArenaAllocator` and
`std.heap.FixedBufferAllocator` (`docs/allocator-identity.md`). Allocator `a` is
`Mem.allocators[a]`; each of its blocks has kind `.owned a`, so the kind of a block records
the allocator that owns it.

* A free or remap through an allocator of a block that another allocator made throws
  `.illegal`: `rawFree`/`poisonFree` need `.heap`, `ownedFree`/`ownedRemapBytes` need
  `.owned a`, and `AllocRef.remap` checks the owner first (the default failing
  `Allocator.remap` does not inspect the block).
* A free through an arena ends the lifetime of the block (the `Allocator` contract). Zig 0.16
  gives the bytes back only for the last allocation; the arena model has no capacity, so that
  has no other effect.
* `Owned.reset` (`ArenaAllocator.reset`, `FixedBufferAllocator.reset`) ends the lifetime of
  exactly the blocks of the allocator; `Arena.deinit` also ends the allocator.
* A fixed buffer of `cap` bytes at address `base` has Zig's `end_index` (`OwnedAlloc.used`):
  an allocation pads to the alignment of `base + used` and fails if it does not fit; a free of
  the last allocation gives its bytes back (LIFO), a free of another one does not.
* An arena request is an allocation attempt of `Mem.allocPolicy`/`Mem.failAt`, as `rawAlloc`:
  every arena request may fail (Zig asks the child allocator only for a new node).

Remap keeps lengths and shrinks in place; growth fails (Zig grows the last allocation in place
when it fits, M02). Owned blocks get fresh model addresses, not addresses inside the buffer or
the arena's nodes, unless the opt-in reuse policy (`AllocPolicy.reuseAddr`, M05) gives one the
address of a freed or reset block. Reset and deinit record no access for the race check: like Zig's,
they are not thread-safe.
-/

namespace Zig

/-- An allocator: the model's `std.mem.Allocator` (blocks of kind `.heap`) or allocator `a`. -/
inductive AllocRef where
  | std
  | owned (a : AllocId)
  deriving DecidableEq, Repr, Inhabited

/-- The kind of the blocks of an allocator. -/
def AllocRef.kind : AllocRef → BlockKind
  | .std => .heap
  | .owned a => .owned a

/-- The state of the live allocator `a`. An unknown or deinitialized one throws `.illegal`. -/
def ownedState (a : AllocId) : MemM OwnedAlloc := do
  match (← get).allocators[a]? with
  | some st => if st.live then pure st else throw .illegal
  | none => throw .illegal

def setOwned (a : AllocId) (st : OwnedAlloc) : MemM Unit :=
  modify fun m => { m with allocators := m.allocators.set! a st }

/-- A new allocator with the policy `p`. -/
def Owned.init (p : OwnedPolicy) : MemM AllocId := do
  let m ← get
  set { m with allocators := m.allocators.push { policy := p } }
  pure m.allocators.size

/-- `ArenaAllocator.init(child)`, over the model's `std.mem.Allocator`. -/
def Arena.init : MemM AllocId := Owned.init .arena

/-- `FixedBufferAllocator.init(buffer)`, for a buffer of `cap` bytes at address `base`. -/
def FixedBuffer.init (base cap : Nat) : MemM AllocId := Owned.init (.fixedBuffer base cap)

/-- The buffer index of an allocation of `n` bytes with alignment `align` after `used`
bytes, and the new `used`: Zig's `alignPointerOffset` from the buffer's address. -/
def fixedBufferNext (base used align n : Nat) : Nat × Nat :=
  let start := alignUp (base + used) align - base
  (start, start + n)

/-- A request of `n > 0` bytes from allocator `a`. `none`: the allocation fails. -/
def ownedRawAlloc (a : AllocId) (n align : Nat) : MemM (Option Ptr) := do
  let st ← ownedState a
  match st.policy with
  | .arena =>
    let m ← get
    set { m with allocs := m.allocs + 1 }
    if m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures
    then return none
    some <$> alloc (.owned a) n align
  | .fixedBuffer base cap =>
    let (start, used) := fixedBufferNext base st.used align n
    if cap < used then return none
    let b := (← get).blocks.size
    let p ← alloc (.owned a) n align
    setOwned a { st with used, starts := (b, start) :: st.starts }
    return some p

/-- `allocBytes` through allocator `a`. -/
def ownedAllocBytes (a : AllocId) (align n : Nat) : MemM (Except ErrName Ptr) := do
  if n = 0 then return .ok (zeroAllocPtr align)
  match ← ownedRawAlloc a n align with
  | some p => pure (.ok p)
  | none => pure (.error "OutOfMemory")

/-- `p` is the start of a live block of `n` bytes and of kind `k`; else `.illegal`. -/
def wholeBlock (k : BlockKind) (p : Ptr) (n : Nat) : MemM (BlockId × Block) := do
  let (b, blk, o) ← (← get).access p n 1
  if blk.kind = k ∧ o = 0 ∧ blk.bytes.size = n then pure (b, blk) else throw .illegal

/-- A fixed buffer gives `k` bytes back when block `b` of `len` bytes is its last allocation
(`isLastAllocation`); an arena has no capacity to give back. -/
def giveBack (a : AllocId) (st : OwnedAlloc) (b : BlockId) (len k : Nat) : MemM Unit :=
  match st.policy with
  | .arena => pure ()
  | .fixedBuffer .. =>
    if (st.starts.lookup b).map (· + len) = some st.used then
      setOwned a { st with used := st.used - k }
    else pure ()

/-- `rawFree` through allocator `a`, after the poison write of `Allocator.free`: `p` is the
start of a live block of `n` bytes of `a`. A fixed buffer gives the bytes of its last
allocation back. -/
def ownedFree (a : AllocId) (p : Ptr) (n : Nat) : MemM Unit := do
  let st ← ownedState a
  let (b, _) ← wholeBlock (.owned a) p n
  recordAccess b 0 n .write
  free p
  giveBack a st b n n

/-- The memory with every block of allocator `a` dead. -/
def Mem.resetOwned (m : Mem) (a : AllocId) : Mem :=
  { m with blocks := m.blocks.map fun blk =>
      if blk.kind = .owned a then { blk with live := false } else blk }

/-- `ArenaAllocator.reset(mode)` and `FixedBufferAllocator.reset()`: every block of `a` is dead,
and a fixed buffer is empty again. The arena's boolean result (only a capacity hint) is not
modelled. -/
def Owned.reset (a : AllocId) : MemM Unit := do
  let st ← ownedState a
  modify (·.resetOwned a)
  setOwned a { st with used := 0, starts := [] }

/-- `ArenaAllocator.deinit()`: every block is dead, and so is the arena. -/
def Arena.deinit (a : AllocId) : MemM Unit := do
  Owned.reset a
  let st ← ownedState a
  setOwned a { st with live := false }

/-- `remap` through allocator `a` of the whole live block `s` (bytes `len` to `n`): the same
or a smaller length succeeds in place, and a fixed buffer gives the bytes back for its last
allocation; growth fails. -/
def ownedRemapBytes (a : AllocId) (s : Slice) (len n : Nat) : MemM (Option Slice) := do
  let st ← ownedState a
  let (b, blk) ← wholeBlock (.owned a) s.ptr len
  if len < n then return none
  recordAccess b 0 len .write
  let m ← get
  set { m with blocks := m.blocks.set! b { blk with bytes := blk.bytes.extract 0 n } }
  giveBack a st b len (len - n)
  return some s

/-! ## `std.mem.Allocator` calls on an allocator -/

/-- `create(T)`. -/
def AllocRef.create (r : AllocRef) (size align : Nat) : MemM (Except ErrName Ptr) :=
  match r with
  | .std => Allocator.create ⟨⟩ size align
  | .owned a => ownedAllocBytes a align size

/-- `destroy(p)`. -/
def AllocRef.destroy (r : AllocRef) (size : Nat) (p : Ptr) : MemM Unit :=
  match r with
  | .std => Allocator.destroy ⟨⟩ size p
  | .owned a => if size = 0 then pure () else ownedFree a p size

/-- `alloc(T, n)`. -/
def AllocRef.alloc (r : AllocRef) (size align : Nat) (n : BitVec 64) :
    MemM (Except ErrName Slice) :=
  match r with
  | .std => Allocator.alloc ⟨⟩ size align n
  | .owned a => do
    if 2 ^ 64 ≤ size * n.toNat then return .error "OutOfMemory"
    match ← ownedAllocBytes a align (size * n.toNat) with
    | .ok p => pure (.ok ⟨p, n⟩)
    | .error e => pure (.error e)

/-- `free(s)`. -/
def AllocRef.free (r : AllocRef) (size : Nat) (s : Slice) : MemM Unit :=
  match r with
  | .std => Allocator.free ⟨⟩ size s
  | .owned a => if size * s.len.toNat = 0 then pure () else ownedFree a s.ptr (size * s.len.toNat)

/-- `remap(s, n)`. A new length of 0 frees `s`. A nonempty `s` must be a whole live block of
`r` first: `Allocator.remap` leaves a failing request unchecked. -/
def AllocRef.remap (r : AllocRef) (size : Nat) (s : Slice) (n : BitVec 64) :
    MemM (Option Slice) := do
  if size * s.len.toNat ≠ 0 then discard <| wholeBlock r.kind s.ptr (size * s.len.toNat)
  match r with
  | .std => Allocator.remap ⟨⟩ size s n
  | .owned a => do
    if n.toNat = 0 then
      AllocRef.free (.owned a) size s
      return some ⟨s.ptr, 0⟩
    if s.len.toNat = 0 then return none
    if size = 0 then return some ⟨s.ptr, n⟩
    if 2 ^ 64 ≤ size * n.toNat then return none
    match ← ownedRemapBytes a s (size * s.len.toNat) (size * n.toNat) with
    | some _ => pure (some ⟨s.ptr, n⟩)
    | none => pure none

end Zig
