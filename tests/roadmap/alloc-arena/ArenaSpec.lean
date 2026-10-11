import AllocArena.ArenaLinux
import AllocArena.Core

/-!
# The translated `ArenaAllocator`'s `free`, `resize` and `remap` against `FAllocSpec`

`free_spec`, `resize_spec`, `remap_spec`: the entries of the translated `std.heap.ArenaAllocator`
(Zig 0.16.0, x86_64-linux, `AllocArena/ArenaLinux.lean`) meet `FAllocSpec`'s contracts for the
arena invariant `inv CI γ e ctx` below, read in the caller's thread (`CTriple`, `Sched.soloRun`),
from the generated code only. No model of the arena is used. `alloc` is not here: the stock arena
does not meet `FAllocSpec`'s `alloc` field for any child (O-E, O-B in `docs/alloc-arena.md`).

**The invariant** `own CI γ e ctx` (for a child allocator invariant `CI`, ghost name `γ`, epoch `e`):

* the arena struct at `ctx`: the child allocator (16 bytes, not read here), `used_list` and
  `free_list` as pointer-valued atomic words (`aptsE`);
* the ghost authority `gauth γ e M`: the grant map `M` of epoch `e`, grant id ↦ region
  (`docs/sep-full-state.md` §Ghost state);
* the first node of `used_list`, if any (`FirstPart`): its header words (`size` and `end_index`
  atomic, `next` plain), the unused tail of its buffer (from `end_index` on), and the child's
  token for the node; the other used nodes and the free list (`Chain`): headers and tokens, the
  free nodes with their whole buffers;
* the child's state `CI.own`, and `Junk`: bytes that frees which were not the last allocation
  leaked back (any bytes; the arena never touches them until `reset`).

With no first node, `M` is empty. A token for the slice `(p, n)` is `gfrag γ e i (p, n)` for some
grant id `i`: it names exactly that region, so a token of the current epoch shows `M i = some (p,
n)` (`gfrag_mem`), hence a first node: **O-A is excluded by ghost state**, not by a premise, and a
`free` of a slice that this arena did not grant has no token: a permission violation. A token of
an older epoch (after `reset`) is stale: it belongs to `inv … e'` for `e' < e`, whose `own` needs
the authority of epoch `e'`, which no longer exists.

**`free`** loads the first node, compares `buf + end_index` with the slice's end by address
(`ptrEqAddr`), and on a match moves `end_index` back by a strong `cmpxchg`. The comparison is
decided by ownership alone (O-F): a slice of another block lies at disjoint addresses
(`FTriple.apart`, `Mem.LiveDisjoint` in `Mem.FSeq`), and a slice of the node's block that ends at
`buf + end_index` lies past the header, which the arena owns. On a match the slice's bytes rejoin
the tail; otherwise (a grant that is not the last one) they become junk. Either way the grant is
retired (`Upd.retire`).

**`resize`** has the same prefix. A slice that is not the first node's last one only shrinks (the
cut bytes become junk); the last one moves `end_index` back (a shrink: the cut bytes rejoin the
tail) or forward into the tail when it has room (`Node.loadBuf` reads the `size` word:
`FTriple.atomicLoadAs`, `toInt_ofBits`). A successful resize re-points the grant at the new length
(`Upd.reassign`). **`remap`** is `resize` and returns `memory.ptr`.

**O-E** (`ArenaObstruction.oob_free_illegal`): the invariant keeps `end_index` within the first
node's buffer (`OV.Facts`: `24 + ei ≤ sz`). A failed `alloc` leaves it past the buffer, so the reachable
states this specification covers end at the first failed `alloc`.
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaLinux

arena_spec_statements

end AllocArena.ArenaSpec

#print axioms AllocArena.ArenaSpec.free_spec
#print axioms AllocArena.ArenaSpec.resize_spec
#print axioms AllocArena.ArenaSpec.remap_spec
