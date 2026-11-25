# Allocator identity and arenas (M01)

Allocators other than the model's `std.mem.Allocator` (`ZigLean/Mem/Alloc.lean`, blocks of kind
`.heap`) are translated from their Zig code (`--allocator-model translated`,
[allocator-model.md](allocator-model.md)) and proved down to the OS primitives (OSM-01):
`std.heap.FixedBufferAllocator` (`tests/roadmap/alloc-fba`: `FBA.fallocSpec`,
`Client.client_spec`), `std.heap.PageAllocator` (`tests/roadmap/alloc-translated`) and
`std.heap.ArenaAllocator` (`tests/roadmap/alloc-arena`, [alloc-arena.md](alloc-arena.md)). An
allocator's identity is its state and its token in the full-state logic, not a block kind: its
slices lie in the blocks it gets from its child or the OS (`.mapped`, a global or stack buffer), and a
slice it did not grant has no token.

The hand-written model that gave each allocator an id and its blocks the kind `.owned a`
(`ZigLean/Mem/Owned.lean`, `OwnedPolicy`, `OwnedAlloc`, `AllocRef`, `Mem.allocators`, premise
ALC-07) is deleted (steps 1 and 2 of the removal plan in [allocator-model.md](allocator-model.md)),
with its executable regressions (`tests/roadmap/allocator-identity`). No theorem rested on it:
its proof layer (`ZigLean/Sep/Owned.lean`, `ZigLean/Sep/ArenaClient.lean`) was retired before
([alloc-spec.md](alloc-spec.md), "Retired claims").

## Theorems

M01's theorems are stated over the translated `std.heap.ArenaAllocator` in the full-state logic
(`tests/roadmap/alloc-arena`, [alloc-arena.md](alloc-arena.md)):

* cross-allocator frees: a `free`, `resize` or `remap` through the arena needs the arena's token
  of its current epoch, and with it the slice lies past the header of one of the arena's used
  nodes (`Core.granted_in_node`); a slice of another allocator or of an older epoch has no token,
  so no triple admits it. Natively a foreign free panics (`ArenaObstruction.foreign_free_panics`).
* reset: `reset(.free_all)` keeps every other resource (`reset_free_all_frame`, any frame) and
  ends at the next epoch with no grant (`reset_free_all_spec`); `deinit` gives every node back to
  the child (`deinit_ct`). The retaining modes preserve the same ownership contract
  (`reset_retain_capacity_spec`, `reset_retain_with_limit_spec`): the postcondition is
  `reset_free_all_spec`'s, the next epoch with no grant. The internal `loop66_ct` gives every
  node back to the child except at most one per list, which is kept as it is, shrunk or grown
  in place, or replaced. The amount of retained capacity and its relation to the limit are NOT
  stated (open: engine-ledger row `arena-retained-capacity`).
* the production-style session client: pending. It is to be proved once over `FAllocSpec` and a
  reset ledger for every allocator, and is blocked on `alloc`: the stock arena meets `FAllocSpec`'s
  `alloc` for no child (O-E, O-B) and the patched arena's `alloc` is not proved yet.

## Limits

* In `std` mode the translator does not route `std.heap` allocator calls: those programs use
  one `std.mem.Allocator` and their `heap.*` calls stay rejected. `--allocator-model translated`
  translates the allocators themselves.
* Custom allocators have no hand-written model; E01 external contracts remain the route for an
  allocator from outside the program.

Checks: `bash tests/roadmap/alloc-arena/check.sh` runs the translated arena's executable
regressions (`AllocArena/Eval.lean`, against the native run) and prints the axioms of the M01
theorems over it.
