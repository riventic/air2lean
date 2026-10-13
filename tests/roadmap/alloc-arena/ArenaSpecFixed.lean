import AllocArena.ArenaFixedLinux
import AllocArena.Core

/-!
# The patched `ArenaAllocator`'s `free`, `resize` and `remap` against `FAllocSpec`

The same statements as `ArenaSpec.lean` for the arena of `upstream/arena-fix.patch`
(`AllocArena/ArenaFixedLinux.lean`), with the same invariant (`AllocArena.Core`). The patched
`free` and `resize` load the node's size after `end_index` and return when `end_index` is past
the buffer (a racing `alloc`'s reservation, `docs/upstream/arena-oob-gep.md`); the invariant keeps
`end_index` within the buffer, so they go on as the stock ones do (`arena_bounds`).
-/

namespace AllocArena.ArenaSpecFixed

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaFixedLinux

arena_spec_statements checked

end AllocArena.ArenaSpecFixed

#print axioms AllocArena.ArenaSpecFixed.free_spec
#print axioms AllocArena.ArenaSpecFixed.resize_spec
#print axioms AllocArena.ArenaSpecFixed.remap_spec
