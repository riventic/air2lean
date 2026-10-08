import ZigLean.Mem.Alloc

/-!
# OS page mappings: `posix.mmap`, `posix.munmap`, `posix.mremap` (premise OS-01)

The trusted base of the allocator proofs (`docs/os-mmap.md`). Every allocator above these three
calls (`std.heap.PageAllocator`, arenas, user allocators) is translated from its Zig code; only the
calls below are modelled. The signatures are Zig 0.16.0's (`lib/std/posix.zig`):

* `mmap(ptr: ?[*]align(page_size_min) u8, length: usize, prot: PROT, flags: MAP, fd: fd_t,
  offset: u64) MMapError![]align(page_size_min) u8` — `Os.mmap`;
* `munmap(memory: []align(page_size_min) const u8) void` — `Os.munmap`;
* `mremap(old_address: ?[*]align(page_size_min) u8, old_len: usize, new_len: usize,
  flags: MREMAP, new_address: ?[*]align(page_size_min) u8) MRemapError![]align(page_size_min) u8`
  (Linux only) — `Os.mremap`.

`PROT`, `MAP` and `MREMAP` are `packed struct(u32)`s: the model takes their backing integers.

**mmap.** Only an anonymous private read-write mapping is modelled: `prot = READ|WRITE`,
`flags = PRIVATE|ANONYMOUS` (the profile's encoding), `fd = -1`, `offset = 0`. Any other
combination throws `.unspecified` (outside the model). The hint is ignored (the kernel may ignore
a hint without `MAP.FIXED`). A length of 0 is `EINVAL`, which Zig maps to `unreachable`:
`.illegal`. Otherwise the request is one allocation attempt (`Mem.allocs`); the allocator failure
decision (`Mem.mapDenied`, the same decision as `rawAlloc`'s: `failAt`, `failures`, `maxBytes`,
the oracle `fails`, `budget`) fails it with the `MMapError` that `AllocPolicy.os.mmapError` picks,
and leaves every block unchanged. A success is a new block of kind `.mapped 0`: exactly `length`
zero bytes, at a page-aligned address above every earlier block; the next block starts above the
mapping's last page (fresh addresses: no address is reused).

**munmap.** `memory` must be a page-aligned range `[off, off + alignUp len page)` of one live
mapping with live offsets `[lo, hi)` (`BlockKind.mapped lo`, `hi` its byte count), and `len > 0`:
the whole mapping (it ends), a prefix (`lo` moves to the range's end), or a tail (the bytes end at
`off`). The end of the mapping counts as its page end (`lo + alignUp (hi - lo) page`). Anything
else is `.illegal`: a range in the middle (Zig's `munmap` rejects it too), a range past the
mapping, a pointer that is not into a live mapping (double `munmap`, a heap block, no block). The
kernel would accept some of these (unmapping nothing, or someone else's pages); the model treats
them as illegal behaviour, which only makes the proofs of their absence stronger. The removed bytes
are recorded as a write (a concurrent access races).

**mremap** (Linux only; on a profile without `mremap` it throws `.unspecified`). `flags` may only
be `0` or `MAYMOVE` and `new_address` must be null (`FIXED`/`DONTUNMAP` are outside the model:
`.unspecified`). `old_address`/`old_len` must name a whole live mapping (as for `munmap`'s whole
case), else `.illegal`. `new_len = 0` returns `error.InvalidSyscallParameters` (`EINVAL`).
A shrink stays in place. A growth is an allocation attempt: the failure decision fails it with the
`MRemapError` that `AllocPolicy.os.mremapError` picks; otherwise it grows in place when no other
block lies above the mapping and the oracle `mremapMoves` does not move it, or moves to a fresh
mapping under `MAYMOVE`; without `MAYMOVE` and with no room it returns `error.OutOfMemory`. A moved
mapping copies the live bytes and ends the old block. The grown bytes up to the old page end are
undefined (the kernel keeps the stale tail of the last page), the rest are zero.

**Page size.** A parameter of the target profile (`Os.Profile`), comptime in Zig 0.16.0's
`page_allocator` for both modelled targets: 4 KiB on `x86_64-linux`, 16 KiB on `aarch64-macos`.
-/

namespace Zig

namespace Os

/-- The target-dependent constants of the page-mapping model. -/
structure Profile where
  /-- `std.heap.pageSize()`; positive. -/
  pageSize : Nat
  /-- `PROT{ .READ = true, .WRITE = true }`'s backing integer. -/
  protReadWrite : BitVec 32 := 3
  /-- `MAP{ .TYPE = .PRIVATE, .ANONYMOUS = true }`'s backing integer. -/
  mapPrivateAnonymous : BitVec 32
  /-- `posix.MREMAP != void`. -/
  hasMremap : Bool
  deriving Repr, DecidableEq

/-- `x86_64-linux`: 4 KiB pages, `MAP.PRIVATE = 0x02`, `MAP.ANONYMOUS = 0x20`, `mremap`. -/
def Profile.linuxX86_64 : Profile :=
  { pageSize := 4096, mapPrivateAnonymous := 0x22, hasMremap := true }

/-- `aarch64-macos`: 16 KiB pages, `MAP.PRIVATE = 0x02`, `MAP.ANONYMOUS = 0x1000`, no
`mremap`. -/
def Profile.macosAarch64 : Profile :=
  { pageSize := 16384, mapPrivateAnonymous := 0x1002, hasMremap := false }

/-- `fd = -1`. -/
def noFd : BitVec 32 := BitVec.allOnes 32

/-- `MREMAP{ .MAYMOVE = true }`'s backing integer. -/
def mremapMayMove : BitVec 32 := 1

end Os

/-- The Zig error name. -/
def MmapError.name : MmapError → ErrName
  | .memoryMappingNotSupported => "MemoryMappingNotSupported"
  | .accessDenied => "AccessDenied"
  | .permissionDenied => "PermissionDenied"
  | .lockedMemoryLimitExceeded => "LockedMemoryLimitExceeded"
  | .processFdQuotaExceeded => "ProcessFdQuotaExceeded"
  | .systemFdQuotaExceeded => "SystemFdQuotaExceeded"
  | .outOfMemory => "OutOfMemory"
  | .mappingAlreadyExists => "MappingAlreadyExists"
  | .unexpected => "Unexpected"

/-- The Zig error name. -/
def MremapError.name : MremapError → ErrName
  | .lockedMemoryLimitExceeded => "LockedMemoryLimitExceeded"
  | .invalidSyscallParameters => "InvalidSyscallParameters"
  | .outOfMemory => "OutOfMemory"
  | .unexpected => "Unexpected"

/-- `posix.MMapError`'s names. -/
def mmapErrorNames : List ErrName :=
  ["MemoryMappingNotSupported", "AccessDenied", "PermissionDenied", "LockedMemoryLimitExceeded",
    "ProcessFdQuotaExceeded", "SystemFdQuotaExceeded", "OutOfMemory", "MappingAlreadyExists",
    "Unexpected"]

/-- `posix.MRemapError`'s names. -/
def mremapErrorNames : List ErrName :=
  ["LockedMemoryLimitExceeded", "InvalidSyscallParameters", "OutOfMemory", "Unexpected"]

/-- The allocator failure decision for a request of `n` bytes at attempt `m.allocs`: `rawAlloc`'s
(`Mem.allocDenied`), as a `Bool`. -/
def Mem.mapDenied (m : Mem) (n : Nat) : Bool :=
  decide (m.failAt = some m.allocs) || decide (m.allocPolicy.maxBytes < n) ||
    decide (m.allocs ∈ m.allocPolicy.failures) || m.oracleDenies n

/-- The memory after a successful `mmap` of `n` bytes with page size `P`: a new `.mapped 0` block
of `n` zero bytes at the next page-aligned address; the next block starts above its last page. -/
def Mem.afterMmap (m : Mem) (P n : Nat) : Mem :=
  { m with
    blocks := m.blocks.push
      { bytes := Array.replicate n (.int 0), align := P, kind := .mapped 0, live := true,
        addr := alignUp m.nextAddr P }
    nextAddr := alignUp m.nextAddr P + alignUp n P + 1 }

/-- The bytes that a growth from `cur` to `n` live bytes adds: undefined up to the old page end,
zero after it. -/
def mremapFill (P cur n : Nat) : Array Byte :=
  (Array.range (n - cur)).map fun j => if cur + j < alignUp cur P then .undef else .int 0

/-- No block other than `b` reaches up to `blk`'s address: the mapping can grow in place. -/
def Mem.mappingOnTop (m : Mem) (b : BlockId) (blk : Block) : Bool :=
  m.blocks.zipIdx.all fun (o, j) => j == b || decide (o.addr + o.bytes.size < blk.addr)

namespace Os

/-- `posix.mmap` (module doc). -/
def mmap (os : Profile) (_hint : Option Ptr) (len : BitVec 64) (prot flags fd : BitVec 32)
    (offset : BitVec 64) : MemM (Except ErrName Slice) := do
  if prot ≠ os.protReadWrite ∨ flags ≠ os.mapPrivateAnonymous ∨ fd ≠ noFd ∨ offset ≠ 0 then
    throw .unspecified
  if len.toNat = 0 then throw .illegal
  let m ← get
  set { m with allocs := m.allocs + 1 }
  if m.mapDenied len.toNat then
    return .error (m.allocPolicy.os.mmapError m.allocs len.toNat).name
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
def munmap (os : Profile) (memory : Slice) : MemM Unit := do
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
    blocks := m.blocks.set! b { blk with bytes := blk.bytes ++ mremapFill P (blk.bytes.size - lo) n }
    nextAddr := Nat.max m.nextAddr (blk.addr + lo + alignUp n P + 1) }

/-- The memory after moving mapping block `b` (live from `lo`) to a fresh block of `n` live bytes:
the old block ends, the new one is at the next page-aligned address. -/
def _root_.Zig.Mem.mremapMoved (m : Mem) (P : Nat) (b : BlockId) (blk : Block) (lo n : Nat) : Mem :=
  { m with
    blocks := (m.blocks.set! b { blk with live := false }).push
      { bytes := blk.bytes.extract lo blk.bytes.size ++ mremapFill P (blk.bytes.size - lo) n,
        align := P, kind := .mapped 0, live := true, addr := alignUp m.nextAddr P }
    nextAddr := alignUp m.nextAddr P + alignUp n P + 1 }

/-- `mremap` of the whole live mapping `b` (from `lo`) at `p` to `newLen` bytes, after the
argument checks (module doc). -/
def mremapLive (os : Profile) (p : Ptr) (b : BlockId) (blk : Block) (lo : Nat) (newLen : BitVec 64)
    (flags : BitVec 32) : MemM (Except ErrName Slice) := do
  let P := os.pageSize
  let hi := blk.bytes.size
  let cur := hi - lo
  let n := newLen.toNat
  if n = 0 then return .error MremapError.invalidSyscallParameters.name
  if n ≤ cur then
    recordAccess b (lo + n) (hi - (lo + n)) .write
    modify fun m => m.mremapShrunk b blk lo n
    return .ok ⟨p, newLen⟩
  let m ← get
  set { m with allocs := m.allocs + 1 }
  if m.mapDenied n then
    return .error (m.allocPolicy.os.mremapError m.allocs n).name
  let onTop := m.mappingOnTop b blk
  if flags = mremapMayMove ∧ (m.allocPolicy.os.mremapMoves m.allocs n ∨ onTop = false) then
    recordAccess b lo cur .write
    let m₁ ← get
    set (m₁.mremapMoved P b blk lo n)
    return .ok ⟨⟨some m₁.blocks.size, 0⟩, newLen⟩
  if onTop = false then return .error MremapError.outOfMemory.name
  modify fun m => m.mremapGrown P b blk lo n
  return .ok ⟨p, newLen⟩

/-- `posix.mremap` (module doc). -/
def mremap (os : Profile) (oldAddress : Option Ptr) (oldLen newLen : BitVec 64) (flags : BitVec 32)
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
