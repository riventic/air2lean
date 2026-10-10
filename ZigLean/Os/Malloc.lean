import ZigLean.Os.Env
import ZigLean.Mem.Alloc

/-!
# macOS `malloc`, `free`, `malloc_size` (premise OSM-02)

`std.heap.c_allocator` (Zig 0.16.0, `lib/std/heap.zig`) calls libc's `malloc` and `free`, and
`malloc_size` in `resize`; `std.Thread.spawn` on macOS (`PosixThreadImpl.spawn`) boxes the
thread's arguments with it (user decision D1, 2026-10-09: libc `malloc`/`free` are a trusted
primitive). Under `--thread-model translated` the translator binds the `extern "c"` symbols to the
definitions below; `c_allocator` itself is translated.

A `malloc` block is a block of the model heap (kind `.heap`), made by the allocator machinery of
`ZigLean/Mem/Alloc.lean` (`rawAlloc`): one attempt index (`Mem.allocs`) and one failure decision
(`Mem.allocDenied`: `failAt`, `failures`, `maxBytes`, the oracle `fails`, the live-heap
`budget`) for every allocation. So libc's heap and the model's `std.mem.Allocator` heap are the
same heap. `OSM-01` mappings (`.mapped`) are other blocks and never `free`able.

* `malloc(n)`: `null` (the failure decision, `ENOMEM`), or a fresh block of `n + Env.mallocSlack i
  n` undefined bytes (`i` the attempt) at a 16-byte-aligned address. `malloc(0)` is a fresh
  pointer, as on macOS.
* `free(p)`: `null` does nothing. Otherwise `p` must point to offset 0 of a live heap block: the
  block ends, and the free is a write of all its bytes for the race check (a concurrent access
  races). Anything else is `.illegal`: a double free, an inner pointer, a stack, global, mapping
  or arena block, no block.
* `malloc_size(p)`: `0` for `null`, the block's byte count for a live heap block at offset 0,
  else `.illegal` (macOS returns 0 for a pointer it does not own; the model is stricter).

Libc's `malloc` is thread-safe: an allocation is one step with no footprint on the allocator's
own state (OSM-02 states this; audit finding #11 concerns the model's `std.mem.Allocator`, not
libc).
-/

namespace Zig
namespace Os
namespace Darwin

/-- The alignment of every `malloc` block on aarch64-macos. -/
def mallocAlign : Nat := 16

/-- `malloc(usize) ?*anyopaque` (module doc). -/
def malloc (env : Env) (size : BitVec 64) : MemM (Option Ptr) := do
  rawAlloc (size.toNat + env.mallocSlack (← get).allocs size.toNat) mallocAlign

/-- The live heap block that `p` points to the start of, else `.illegal`. -/
def heapBlockAt (p : Ptr) : MemM Block := do
  let some b := p.block | throw .illegal
  let some blk := (← get).blocks[b]? | throw .illegal
  if blk.live ∧ blk.kind = .heap ∧ p.off = 0 then pure blk else throw .illegal

/-- `free(?*anyopaque) void` (module doc). -/
def free (ptr : Option Ptr) : MemM Unit := do
  let some p := ptr | return
  poisonFree p (← heapBlockAt p).bytes.size

/-- `malloc_size(?*const anyopaque) usize` (module doc). -/
def malloc_size (ptr : Option Ptr) : MemM (BitVec 64) := do
  let some p := ptr | return 0
  return BitVec.ofNat 64 (← heapBlockAt p).bytes.size

end Darwin
end Os
end Zig
