import ZigLean.Mem.Enc

/-!
# Allocators

The model of `std.mem.Allocator` (`docs/std-models.md`). The translator does not translate the
functions of `std.mem.Allocator`: a call to one of them becomes a call to the function of the
same name here (`Air2Lean/Memory.lean`'s `allocFn?`).

The model is one allocator, with its state in `Mem`:

* Each allocation gets a new heap block. Allocation number `Mem.failAt` (from 0), every
  index in `Mem.allocPolicy.failures`, requests above `Mem.allocPolicy.maxBytes`, requests the
  oracle `Mem.allocPolicy.fails` rejects and requests beyond `Mem.allocPolicy.budget` fail.
  The default has no failures and no fixed cap; the differential harness selects its 1 MiB
  cap explicitly (`AllocPolicy.harness`). Policies are explicit environment parameters; they
  do not guarantee native allocation success.
* The default `remap` policy fails. Explicit byte policies permit in-place or moved success
  for whole alignment-1 byte blocks; `resize` and other item sizes keep their old behavior.
* A free of a pointer that is not the start of a live heap block, or with a length other than
  the length of the block, throws `.illegal` (a double free, a use after free).

`tests/diff/common.zig`'s `TestAllocator` has the same rules.
-/

namespace Zig

/-- `std.mem.Allocator`. Its state is in `Mem`. -/
structure Allocator where
  deriving DecidableEq, Repr, Inhabited

/-- 16 bytes, the size of `std.mem.Allocator` (two pointers). -/
instance : Enc Allocator where
  size := 16
  align := 8
  encode _ := Array.replicate 16 (.int 0)
  decode _ := pure ⟨⟩

/-- The bytes of the live heap blocks. -/
def Mem.liveHeapBytes (m : Mem) : Nat :=
  m.blocks.foldl (fun acc blk => if blk.live && blk.kind == .heap then acc + blk.bytes.size else acc) 0

/-- The general decision for a request of `n` bytes at attempt `m.allocs`: the oracle fails
it, or the live heap would exceed the budget. The heap is only summed under a budget. -/
def Mem.oracleDenies (m : Mem) (n : Nat) : Bool :=
  m.allocPolicy.fails m.allocs n ||
    match m.allocPolicy.budget with
    | none => false
    | some b => decide (b < m.liveHeapBytes + n)

/-- `rawAlloc` of `n > 0` bytes: allocation number `Mem.allocs`. `none`: the allocation fails. -/
def rawAlloc (n align : Nat) : MemM (Option Ptr) := do
  let m ← get
  set { m with allocs := m.allocs + 1 }
  if m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures then return none
  if m.oracleDenies n then return none
  some <$> alloc .heap n align

/-- The pointer of an allocation of 0 bytes: no block, and the highest address with the
alignment `align`. -/
def zeroAllocPtr (align : Nat) : Ptr := ⟨none, 2 ^ 64 - align⟩

/-- `allocBytesWithAlignment`: `n` undefined bytes. -/
def allocBytes (align n : Nat) : MemM (Except ErrName Ptr) := do
  if n = 0 then return .ok (zeroAllocPtr align)
  match ← rawAlloc n align with
  | some p => pure (.ok p)
  | none => pure (.error "OutOfMemory")

/-- `rawFree` of `n` bytes at `p`: `p` is the start of a live heap block of `n` bytes. -/
def rawFree (p : Ptr) (n : Nat) : MemM Unit := do
  let (_, blk, o) ← (← get).access p n 1
  if blk.kind = .heap ∧ o = 0 ∧ blk.bytes.size = n then free p else throw .illegal

/-- The standard library poisons a freed slice before `rawFree`. Validate the whole heap
block, record that plain write, then free it. The dead bytes need no replacement array. -/
def poisonFree (p : Ptr) (n : Nat) : MemM Unit := do
  let (b, blk, o) ← (← get).access p n 1
  if blk.kind = .heap ∧ o = 0 ∧ blk.bytes.size = n then
    recordAccess b o n .write
    rawFree p n
  else throw .illegal

/-- `create(T)`, for a `T` of `size > 0` bytes and alignment `align`. -/
def Allocator.create (_ : Allocator) (size align : Nat) : MemM (Except ErrName Ptr) :=
  allocBytes align size

/-- `destroy(p)`, for a `*T` with a `T` of `size` bytes. -/
def Allocator.destroy (_ : Allocator) (size : Nat) (p : Ptr) : MemM Unit :=
  if size = 0 then pure () else rawFree p size

/-- `alloc(T, n)` and `alignedAlloc(T, a, n)`: `n` items of `size` bytes. -/
def Allocator.alloc (_ : Allocator) (size align : Nat) (n : BitVec 64) :
    MemM (Except ErrName Slice) := do
  if 2 ^ 64 ≤ size * n.toNat then return .error "OutOfMemory"
  match ← allocBytes align (size * n.toNat) with
  | .ok p => pure (.ok ⟨p, n⟩)
  | .error e => pure (.error e)

/-- Bounded `allocSentinel(u8, n, s)`: one extra byte, a checked store at offset n,
then the payload slice of length n. ReleaseSafe overflow panics before consuming an
allocation-policy decision; even n=0 needs one byte and can fail. -/
def Allocator.allocSentinel (a : Allocator) (n : BitVec 64) (sentinel : BitVec 8) :
    MemM (Except ErrName Slice) := do
  if 2 ^ 64 ≤ n.toNat + 1 then throw .panic
  match ← a.create (n.toNat + 1) 1 with
  | .error e => pure (.error e)
  | .ok p =>
    store 1 (p.add n.toNat) sentinel
    pure (.ok ⟨p, n⟩)

/-- `free(s)`, for items of `size` bytes. Zig first sets the bytes to `undefined`; the block is
dead after the free. The poison write participates in the race check. -/
def Allocator.free (_ : Allocator) (size : Nat) (s : Slice) : MemM Unit :=
  if size * s.len.toNat = 0 then pure () else poisonFree s.ptr (size * s.len.toNat)

/-- `free(s)` of a slice with a sentinel (`[:s]T`): `len + 1` items, the sentinel too
(`mem.absorbSentinel`). -/
def Allocator.freeSentinel (_ : Allocator) (size : Nat) (s : Slice) : MemM Unit :=
  if size = 0 then pure () else poisonFree s.ptr (size * (s.len.toNat + 1))

/-- `dupe(T, m)`: a new block with a copy of the items of `m`. Items of 0 bytes have no bytes to
copy (and the result has no block). -/
def Allocator.dupe (a : Allocator) (size align srcAlign : Nat) (m : Slice) :
    MemM (Except ErrName Slice) := do
  match ← a.alloc size align m.len with
  | .ok s =>
    if size ≠ 0 then memmove size align srcAlign s.ptr m.ptr m.len
    pure (.ok s)
  | .error e => pure (.error e)

/-- Resize byte representations: exact retained prefix, undefined grown suffix.
This copies undefined/pointer-fragment bytes without decoding them. -/
def remapBytes (bs : Array Byte) (n : Nat) : Array Byte :=
  padTo n (bs.extract 0 n)

/-- Every other allocated block, even a dead one, precedes this block's address.
Check this explicitly rather than assuming arbitrary model states have allocation order. -/
def Mem.byteRemapLast (m : Mem) (b : BlockId) (blk : Block) : Bool :=
  b + 1 == m.blocks.size && Nat.allTR m.blocks.size (fun j _ =>
    j == b || decide (m.blocks[j].addr + m.blocks[j].bytes.size < blk.addr))

/-- The in-place byte resize transition; its caller validates whole-block ownership and
latest-block growth before applying it. Thread bookkeeping is retained verbatim. -/
def Mem.afterByteRemap (m : Mem) (b : BlockId) (blk : Block) (n : Nat) : Mem :=
  { m with
    blocks := m.blocks.set! b { blk with bytes := remapBytes blk.bytes n }
    nextAddr := Nat.max m.nextAddr (blk.addr + n + 1) }

/-- Selected successful remap of one whole live heap byte-buffer. Growth in place is
restricted to the latest allocated block, including dead-block history, so addresses
cannot overlap a later block. New allocations stay beyond the enlarged block.
A failed request preserves bytes, logical length and lifetime. -/
def remapByteBuffer (s : Slice) (n : Nat) : MemM (Option Slice) := do
  let m ← get
  if m.allocPolicy.byteRemap = .fail then return none
  let (b, blk, o) ← m.access s.ptr s.len.toNat 1
  if blk.kind ≠ .heap ∨ o ≠ 0 ∨ blk.bytes.size ≠ s.len.toNat then throw .illegal
  if blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n then return none
  match m.allocPolicy.byteRemap with
  | .fail => return none
  | .inPlace =>
    if blk.bytes.size < n ∧ m.byteRemapLast b blk ≠ true then return none
    recordAccess b 0 blk.bytes.size .write
    let current ← get
    set (current.afterByteRemap b blk n)
    return some ⟨s.ptr, BitVec.ofNat 64 n⟩
  | .move =>
    recordAccess b 0 (Nat.min blk.bytes.size n) .read
    let p ← alloc .heap n 1
    storeBytes p 1 (remapBytes blk.bytes n)
    poisonFree s.ptr s.len.toNat
    return some ⟨p, BitVec.ofNat 64 n⟩

/-- `remap(s, n)`: default failure; selected byte policies permit bounded success.
A new length of 0 frees `s`; nonempty zero-size items change length without bytes. -/
def Allocator.remap (a : Allocator) (size : Nat) (s : Slice) (n : BitVec 64) :
    MemM (Option Slice) := do
  if n.toNat = 0 then
    a.free size s
    return some ⟨s.ptr, 0⟩
  if s.len.toNat ≠ 0 ∧ size = 0 then return some ⟨s.ptr, n⟩
  if size = 1 ∧ s.len.toNat ≠ 0 then return ← remapByteBuffer s n.toNat
  return none

end Zig
