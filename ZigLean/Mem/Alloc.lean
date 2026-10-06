import ZigLean.Mem.Enc

/-!
# Allocators

The model of `std.mem.Allocator` (`docs/std-models.md`). The translator does not translate the
functions of `std.mem.Allocator`: a call to one of them becomes a call to the function of the
same name here (`Air2Lean/Memory.lean`'s `allocFn?`).

The model is one allocator, with its state in `Mem`:

* Each allocation gets a new heap block. Allocation number `Mem.failAt` (from 0), every
  index in `Mem.allocPolicy.failures`, and requests above `Mem.allocPolicy.maxBytes` fail.
  The default is the legacy one-failure policy with a 1 MiB request cap. Policies are
  explicit environment parameters; they do not guarantee native allocation success.
* `resize` and `remap` always fail. So `realloc` and a growing `ArrayListUnmanaged` always make
  a new block, copy, and free the old block, and the number of allocations does not depend on
  the allocator.
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

/-- `rawAlloc` of `n > 0` bytes: allocation number `Mem.allocs`. `none`: the allocation fails. -/
def rawAlloc (n align : Nat) : MemM (Option Ptr) := do
  let m ← get
  set { m with allocs := m.allocs + 1 }
  if m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures then return none
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

/-- `remap(s, n)`: the model cannot remap. A new length of 0 frees `s`; items of 0 bytes need no
bytes, so `s` gets the new length. -/
def Allocator.remap (a : Allocator) (size : Nat) (s : Slice) (n : BitVec 64) :
    MemM (Option Slice) := do
  if n.toNat = 0 then
    a.free size s
    return some ⟨s.ptr, 0⟩
  if s.len.toNat ≠ 0 ∧ size = 0 then return some ⟨s.ptr, n⟩
  return none

end Zig
