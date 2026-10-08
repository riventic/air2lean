import ZigLean.Mem.Basic

/-!
# Trusted OS page mapping (`posix.mmap`/`munmap`/`mremap`, premise OS-01)

**Interface owned by P1, bodies owned by P2 (`codex/alloc-translated-p2`).** Under
`--allocator-model translated` (`docs/allocator-model.md`) the translator cuts the call graph at
these three `std.posix` functions, above the syscall (Linux) and libc (macOS) layer, and emits a
call of the matching definition below (`Air2Lean/Check.lean`'s `checkOsCall`,
`Air2Lean/Emit.lean`'s `FCtx.osCall`). They are the only trusted model of a translated
allocator: `std.heap.PageAllocator`, `FixedBufferAllocator` and the `mem.Allocator` wrappers are
translated from their AIR.

The calling convention is fixed here; P2 replaces only the bodies (and may add lemmas):

- `target` selects the OS ABI: how `prot`/`flags` bits decode, and the page size.
- A page-aligned `?[*]align(page) u8` is an `Option Ptr`; a `[]align(page) u8` is a `Slice`.
- `prot`, `flags` (and `mremap`'s flags) are the bits of Zig's packed flag structs
  (`Zig.Packed.toBits`), in the OS's own layout (`os.linux.PROT`/`MAP`/`MREMAP`,
  `macho.vm_prot_t`/`c.MAP`).
- A mapping result is `Except ErrName Slice`. The model may return only `.error "OutOfMemory"`
  (every call site's error set admits it; the checker enforces that); success is a fresh,
  zeroed, page-aligned block of `alignUp len pageSize` bytes, or an oracle failure.
- `munmap` must be called on whole pages of live mappings (whole block, prefix or tail trim);
  anything else is `.illegal` (Zig's `munmap` treats `EINVAL` as unreachable).

Until P2 lands, every call throws `.unspecified`: a generated function that reaches them
elaborates, but no theorem about a successful run can be proved.
-/

namespace Zig.Os

/-- The OS whose `std.posix` ABI a call uses (the profile's target triple). -/
inductive Target where
  | linux
  | macos
  deriving DecidableEq, Repr, Inhabited

/-- `std.heap.page_size_min` of the qualified targets: x86_64-linux and aarch64-macos. -/
def Target.pageSize : Target → Nat
  | .linux => 4096
  | .macos => 16384

/-- `posix.mmap(hint, len, prot, flags, fd, offset)`. P2 stub. -/
def mmap (_target : Target) (_hint : Option Ptr) (_len : BitVec 64) (_prot _flags : BitVec 32)
    (_fd : BitVec 32) (_offset : BitVec 64) : MemM (Except ErrName Slice) :=
  throw .unspecified

/-- `posix.munmap(memory)`. P2 stub. -/
def munmap (_target : Target) (_memory : Slice) : MemM Unit :=
  throw .unspecified

/-- `posix.mremap(old_address, old_len, new_len, flags, new_address)` (Linux only). P2 stub. -/
def mremap (_target : Target) (_old : Option Ptr) (_oldLen _newLen : BitVec 64)
    (_flags : BitVec 32) (_newAddress : Option Ptr) : MemM (Except ErrName Slice) :=
  throw .unspecified

end Zig.Os
