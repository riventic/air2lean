import ZigLean.Mem.Alloc

/-!
# OS page mappings: `posix.mmap`, `posix.munmap`, `posix.mremap` (premise OSM-01)

The trusted base of the allocator proofs (`docs/os-mmap.md`). Under `--allocator-model
translated` (`docs/allocator-model.md`) the translator cuts the call graph at these three
`std.posix` functions and emits a call of the matching definition below (`Air2Lean/Check.lean`'s
`checkOsCall`, `Air2Lean/Emit.lean`'s `FCtx.osCall`). Every allocator above them
(`std.heap.PageAllocator`, arenas, user allocators) is translated from its Zig code. The
signatures are Zig 0.16.0's (`lib/std/posix.zig`):

* `mmap(ptr: ?[*]align(page_size_min) u8, length: usize, prot: PROT, flags: MAP, fd: fd_t,
  offset: u64) MMapError![]align(page_size_min) u8` — `Os.mmap`;
* `munmap(memory: []align(page_size_min) const u8) void` — `Os.munmap`;
* `mremap(old_address: ?[*]align(page_size_min) u8, old_len: usize, new_len: usize,
  flags: MREMAP, new_address: ?[*]align(page_size_min) u8) MRemapError![]align(page_size_min) u8`
  (Linux only) — `Os.mremap`.

`target` selects the OS ABI (flag encodings, page size). A page-aligned `?[*]align(page) u8` is an
`Option Ptr`, a `[]align(page) u8` a `Slice`. `PROT`, `MAP` and `MREMAP` are `packed struct(u32)`s:
the model takes their bits (`Zig.Packed.toBits`), in the OS's own layout. The only error the model
returns is `error.OutOfMemory` (the translator checks that every call site's error set admits it).

**mmap.** Only an anonymous private read-write mapping is modelled: `prot = READ|WRITE`,
`flags = PRIVATE|ANONYMOUS` (the target's encoding), `fd = -1`, `offset = 0`. Any other
combination throws `.unspecified` (outside the model). The hint is ignored (the kernel may ignore
a hint without `MAP.FIXED`). A length of 0 is `EINVAL`, which Zig maps to `unreachable`:
`.illegal`. Otherwise the request is one allocation attempt (`Mem.allocs`); the allocator failure
decision (`Mem.mapDenied`, the same decision as `rawAlloc`'s: `failAt`, `failures`, `maxBytes`,
the oracle `fails`, `budget`) fails it with `error.OutOfMemory` (`ENOMEM`) and leaves every block
unchanged. The premise assumes the kernel fails such a mapping with no other `MMapError` (no
memory locking: no `EAGAIN`). A success is a new block of kind `.mapped 0`: exactly `length` zero
bytes, at the placement's address for its pages (`Mem.newAddr` of `alignUp length page` bytes with
page alignment, `docs/address-placement.md`): any page-aligned address whose pages stay below 2^64
and clear of every live block, a freed mapping's included (the kernel reuses addresses). A mapping
whose pages would end above the target's user address space (`Os.Target.addrLimit`) fails with
`error.OutOfMemory` instead: the kernel never maps there.

**munmap.** `memory` must be a page-aligned range `[off, off + alignUp len page)` of one live
mapping with live offsets `[lo, hi)` (`BlockKind.mapped lo`, `hi` its byte count), and `len > 0`:
the whole mapping (it ends), a prefix (`lo` moves to the range's end), or a tail (the bytes end at
`off`). The end of the mapping counts as its page end (`lo + alignUp (hi - lo) page`). Anything
else is `.illegal`: a range in the middle (Zig's `munmap` rejects it too), a range past the
mapping, a pointer that is not into a live mapping (double `munmap`, a heap block, no block). The
kernel would accept some of these (unmapping nothing, or someone else's pages); the model treats
them as illegal behaviour, which only makes the proofs of their absence stronger. The removed bytes
are recorded as a write (a concurrent access races).

**mremap** (Linux only; on macOS, where `posix.MREMAP` is `void`, it throws `.unspecified`). `flags` may only
be `0` or `MAYMOVE` and `new_address` must be null (`FIXED`/`DONTUNMAP` are outside the model:
`.unspecified`). `old_address`/`old_len` must name a whole live mapping (as for `munmap`'s whole
case), else `.illegal`. `new_len = 0` (`EINVAL`, `error.InvalidSyscallParameters`) is outside the
model: `.unspecified` (the allocator wrappers never pass it). A shrink stays in place. A growth is
an allocation attempt: the failure decision fails it with `error.OutOfMemory`; otherwise it grows in
place when the grown pages are clear of every other live block and end inside the address space
(`Mem.mappingRoom`, `Os.Target.addrLimit`) and the oracle `mremapMoves` does not move it, or
moves to a new mapping at the placement's address under `MAYMOVE`; without `MAYMOVE` and with no
room it returns `error.OutOfMemory`, and so does a move whose pages would end above
`Os.Target.addrLimit`. A moved mapping copies the live bytes and ends the old block. The grown bytes up to the old page end are
undefined (the kernel keeps the stale tail of the last page), the rest are zero.

**Page size.** Fixed per target (`Os.Target.pageSize`), comptime in Zig 0.16.0's
`page_allocator` for both modelled targets: 4 KiB on `x86_64-linux`, 16 KiB on `aarch64-macos`.

**Address space.** No mapping ends above `Os.Target.addrLimit`: `2 ^ 47` on `x86_64-linux`
(`TASK_SIZE_MAX` is a page below it with 4-level paging), and `MACH_VM_MAX_ADDRESS` on
`aarch64-macos` (`0x7FFFFE000000`, `mach/arm/vm_param.h`). Each is at least the kernel's own bound
for a call without a hint above it (5-level-paging Linux maps above 47 bits only for such a
hint); the premise assumes no such hint. Both are far below `2 ^ 64 - 2 ^ 63`, so adding an
alignment `2 ^ k - 1` (`k < 64`) to an address inside a mapping does not overflow.
-/

namespace Zig

namespace Os

/-- The OS whose `std.posix` ABI a call uses (the profile's target triple). -/
inductive Target where
  | linux
  | macos
  deriving DecidableEq, Repr, Inhabited

/-- `std.heap.page_size_min` of the qualified targets: x86_64-linux and aarch64-macos. -/
def Target.pageSize : Target → Nat
  | .linux => 4096
  | .macos => 16384

theorem Target.pageSize_pos (t : Target) : 0 < t.pageSize := by cases t <;> decide

/-- `PROT{ .READ = true, .WRITE = true }`'s bits (`os.linux.PROT`, `macho.vm_prot_t`). -/
def Target.protReadWrite (_ : Target) : BitVec 32 := 3

/-- `MAP{ .TYPE = .PRIVATE, .ANONYMOUS = true }`'s bits: `PRIVATE = 0x02` and `ANONYMOUS = 0x20`
(`os.linux.MAP`), `0x1000` (`c.MAP` on macOS). -/
def Target.mapPrivateAnonymous : Target → BitVec 32
  | .linux => 0x22
  | .macos => 0x1002

/-- The end of the target's user address space: no mapping ends above it (module doc).
`x86_64-linux`: `2 ^ 47` (`TASK_SIZE_MAX` is a page below it). `aarch64-macos`:
`MACH_VM_MAX_ADDRESS` = `0x00007FFFFE000000` (128 TiB - 32 MiB). -/
def Target.addrLimit : Target → Nat
  | .linux => 2 ^ 47
  | .macos => 0x7FFFFE000000

/-- A mapping of `n` bytes at the page-aligned address `a` ends inside the address space. -/
def Target.fits (os : Target) (a n : Nat) : Bool :=
  decide (a + alignUp n os.pageSize ≤ os.addrLimit)

/-- `posix.MREMAP != void`. -/
def Target.hasMremap : Target → Bool
  | .linux => true
  | .macos => false

/-- `fd = -1`. -/
def noFd : BitVec 32 := BitVec.allOnes 32

/-- `MREMAP{ .MAYMOVE = true }`'s backing integer. -/
def mremapMayMove : BitVec 32 := 1

end Os

/-- The allocator failure decision for a request of `n` bytes at attempt `m.allocs`: `rawAlloc`'s
(`Mem.allocDenied`), as a `Bool`. -/
def Mem.mapDenied (m : Mem) (n : Nat) : Bool :=
  decide (m.failAt = some m.allocs) || decide (m.allocPolicy.maxBytes < n) ||
    decide (m.allocs ∈ m.allocPolicy.failures) || m.oracleDenies n

/-- The address of a new mapping of `n` bytes with page size `P`: the placement's address for its
pages (`Mem.newAddr`). -/
def Mem.mapAddr (m : Mem) (P n : Nat) : Nat := m.newAddr (alignUp n P) P

/-- The memory after a successful `mmap` of `n` bytes with page size `P`: a new `.mapped 0` block
of `n` zero bytes at `Mem.mapAddr`. -/
def Mem.afterMmap (m : Mem) (P n : Nat) : Mem :=
  { m with
    blocks := m.blocks.push
      { bytes := Array.replicate n (.int 0), align := P, kind := .mapped 0, live := true,
        addr := m.mapAddr P n } }

/-- The bytes that a growth from `cur` to `n` live bytes adds: undefined up to the old page end,
zero after it. -/
def mremapFill (P cur n : Nat) : Array Byte :=
  (Array.range (n - cur)).map fun j => if cur + j < alignUp cur P then .undef else .int 0

/-- Mapping `b` (`blk`, live from `lo`) can grow in place to `len` bytes of pages: the range
`[blk.addr + lo, blk.addr + lo + len)` ends at or below `L` (the address space,
`Os.Target.addrLimit`) and is clear of every other live block. -/
def Mem.mappingRoom (m : Mem) (L : Nat) (b : BlockId) (blk : Block) (lo len : Nat) : Bool :=
  decide (blk.addr + lo + len ≤ L) &&
    m.blocks.zipIdx.all fun (o, j) => j == b || o.clearOf (blk.addr + lo) len

namespace Os

/-- `posix.mmap` (module doc). -/
def mmap (os : Target) (_hint : Option Ptr) (len : BitVec 64) (prot flags fd : BitVec 32)
    (offset : BitVec 64) : MemM (Except ErrName Slice) := do
  if prot ≠ os.protReadWrite ∨ flags ≠ os.mapPrivateAnonymous ∨ fd ≠ noFd ∨ offset ≠ 0 then
    throw .unspecified
  if len.toNat = 0 then throw .illegal
  let m ← get
  set { m with allocs := m.allocs + 1 }
  if m.mapDenied len.toNat || !os.fits (m.mapAddr os.pageSize len.toNat) len.toNat then
    return .error "OutOfMemory"
  let m₁ ← get
  set (m₁.afterMmap os.pageSize len.toNat)
  return .ok ⟨⟨some m₁.blocks.size, 0⟩, len⟩

/-- How `munmap` of `[off, off + n)` changes a mapping with live offsets `[lo, hi)`, or `none`
(illegal). -/
inductive Unmap where
  | whole
  | prefix (newLo : Nat)
  | tail (newHi : Nat)
  deriving DecidableEq, Repr

/-- The `munmap` case of the page-aligned range `[off, off + alignUp n P)` of a mapping with live
offsets `[lo, hi)`. -/
def unmapCase (P lo hi off n : Nat) : Option Unmap :=
  let E := off + alignUp n P
  let H := lo + alignUp (hi - lo) P
  if n = 0 ∨ off < lo ∨ hi ≤ off ∨ H < E then none
  else if off = lo ∧ E = H then some .whole
  else if off = lo then some (.prefix E)
  else if E = H then some (.tail off)
  else none

/-- The block after an `Unmap`. -/
def Unmap.apply (blk : Block) : Unmap → Block
  | .whole => { blk with live := false }
  | .prefix newLo => { blk with kind := .mapped newLo }
  | .tail newHi => { blk with bytes := blk.bytes.extract 0 newHi }

/-- The live mapping that `p` points into: its block id, block and first live offset. -/
def mappingAt (p : Ptr) : MemM (BlockId × Block × Nat) := do
  match p.block with
  | none => throw .illegal
  | some b =>
    match (← get).blocks[b]? with
    | none => throw .illegal
    | some blk =>
      match blk.kind with
      | .mapped lo => if blk.live ∧ 0 ≤ p.off then pure (b, blk, lo) else throw .illegal
      | _ => throw .illegal

/-- `posix.munmap` (module doc). -/
def munmap (os : Target) (memory : Slice) : MemM Unit := do
  let (b, blk, lo) ← mappingAt memory.ptr
  let off := memory.ptr.off.toNat
  if (blk.addr + off) % os.pageSize ≠ 0 then throw .illegal
  match unmapCase os.pageSize lo blk.bytes.size off memory.len.toNat with
  | none => throw .illegal
  | some u =>
    recordAccess b off (Nat.min (off + alignUp memory.len.toNat os.pageSize) blk.bytes.size - off)
      .write
    let m ← get
    set { m with blocks := m.blocks.set! b (u.apply blk) }

/-- The memory after an in-place shrink of mapping block `b` to `lo + n` bytes. -/
def _root_.Zig.Mem.mremapShrunk (m : Mem) (b : BlockId) (blk : Block) (lo n : Nat) : Mem :=
  { m with blocks := m.blocks.set! b { blk with bytes := blk.bytes.extract 0 (lo + n) } }

/-- The memory after an in-place growth of mapping block `b` (live from `lo`) to `n` live bytes. -/
def _root_.Zig.Mem.mremapGrown (m : Mem) (P : Nat) (b : BlockId) (blk : Block) (lo n : Nat) : Mem :=
  { m with
    blocks := m.blocks.set! b { blk with bytes := blk.bytes ++ mremapFill P (blk.bytes.size - lo) n } }

/-- The memory after moving mapping block `b` (live from `lo`) to a new block of `n` live bytes:
the old block ends, the new one is at `Mem.mapAddr`, chosen while the old one is still mapped. -/
def _root_.Zig.Mem.mremapMoved (m : Mem) (P : Nat) (b : BlockId) (blk : Block) (lo n : Nat) : Mem :=
  { m with
    blocks := (m.blocks.set! b { blk with live := false }).push
      { bytes := blk.bytes.extract lo blk.bytes.size ++ mremapFill P (blk.bytes.size - lo) n,
        align := P, kind := .mapped 0, live := true, addr := m.mapAddr P n } }

/-- `mremap` of the whole live mapping `b` (from `lo`) at `p` to `newLen` bytes, after the
argument checks (module doc). -/
def mremapLive (os : Target) (p : Ptr) (b : BlockId) (blk : Block) (lo : Nat) (newLen : BitVec 64)
    (flags : BitVec 32) : MemM (Except ErrName Slice) := do
  let P := os.pageSize
  let hi := blk.bytes.size
  let cur := hi - lo
  let n := newLen.toNat
  if n = 0 then throw .unspecified
  if n ≤ cur then
    recordAccess b (lo + n) (hi - (lo + n)) .write
    modify fun m => m.mremapShrunk b blk lo n
    return .ok ⟨p, newLen⟩
  let m ← get
  set { m with allocs := m.allocs + 1 }
  if m.mapDenied n then
    return .error "OutOfMemory"
  let room := m.mappingRoom os.addrLimit b blk lo (alignUp n P)
  if flags = mremapMayMove ∧ (m.allocPolicy.os.mremapMoves m.allocs n ∨ room = false) then
    if !os.fits (m.mapAddr P n) n then return .error "OutOfMemory"
    recordAccess b lo cur .write
    let m₁ ← get
    set (m₁.mremapMoved P b blk lo n)
    return .ok ⟨⟨some m₁.blocks.size, 0⟩, newLen⟩
  if room = false then return .error "OutOfMemory"
  modify fun m => m.mremapGrown P b blk lo n
  return .ok ⟨p, newLen⟩

/-- `posix.mremap` (module doc). -/
def mremap (os : Target) (oldAddress : Option Ptr) (oldLen newLen : BitVec 64) (flags : BitVec 32)
    (newAddress : Option Ptr) : MemM (Except ErrName Slice) := do
  if os.hasMremap = false ∨ newAddress ≠ none ∨ (flags ≠ 0 ∧ flags ≠ mremapMayMove) then
    throw .unspecified
  let p ← match oldAddress with
    | none => throw .illegal
    | some p => pure p
  let (b, blk, lo) ← mappingAt p
  if p.off.toNat ≠ lo ∨ oldLen.toNat = 0 ∨
      alignUp oldLen.toNat os.pageSize ≠ alignUp (blk.bytes.size - lo) os.pageSize then
    throw .illegal
  mremapLive os p b blk lo newLen flags

end Os

end Zig
