import AllocArena.ArenaLinux
import ZigLean.Sep.Full.Conc

/-!
# Obstructions O-A and O-E (kernel-checked)

## O-A: a foreign `free` on an empty arena panics

`ArenaAllocator.free` (Zig 0.16.0) starts with `const node = arena.loadFirstNode().?;`. On an
arena that has no node (`used_list == null`: a fresh arena, or one after `reset(.free_all)`) the
unwrap panics, whatever slice is freed. `resize` (and so `remap`) start the same way.
`arena_foreign_free` (`arena.zig`) frees a slice of the child `FixedBufferAllocator` through a
fresh arena: the translated program panics, as the native one does
(`panic: attempt to use null value`, `ArenaAllocator.zig:615`).

So an `FAllocSpec` invariant `I` of the arena that holds for an empty arena must make
`I.own ⋆ I.granted p k bs` unsatisfiable there: the token must say that the arena issued the region
in its current generation. Full-state resources (`ZigLean/Sep/Full/Res.lean`) have owned bytes
and duplicable block knowledge only, so a token cannot be revoked by a reset or tied to the
arena's current node list: it needs ghost state (an authoritative node set in `own`, a fragment
per region in `tok`). Without it, `ArenaSpec.lean` proves `free`, `resize` and `remap` for an
arena that has a node (`used_list = some N`), where any slice is harmless.

## O-E: `free` after a failed `alloc` forms an out-of-bounds pointer

An `alloc` that does not fit the first node bumps its `end_index` past the buffer; if the child
then fails, that node stays first. `free` computes `buf_ptr + end_index` (a many-pointer
addition: `getelementptr inbounds` natively, `Zig.ptrProject` here), which lies outside the
node's block: `.illegal` (MM-3), and undefined behaviour natively
(`docs/upstream/arena-oob-gep.md`). `arena_oob_free` builds that state by hand (a 64-byte node
with `end_index = 1000`), because the kernel does not evaluate the translated `alloc` (a
`partial_fixpoint` group), and frees a foreign slice.
-/

namespace AllocArena.ArenaObstruction

open Zig AllocArena.ArenaLinux

/-- The one-thread schedule of a whole program (oracle `0`). -/
def solo {α : Type} (main : ConcM Tgt α) : Option (Except Error α) :=
  ((Sched.run dispatch 100000 (fun _ => 0) main (mem0 .fresh)).run).map fun r => r.map (·.1)

/-- **O-A.** Freeing a foreign slice through a fresh arena panics. -/
theorem foreign_free_panics : solo arena_foreign_free = some (.error .panic) := by
  decide +kernel

/-- **O-E.** `free` in the state that a failed `alloc` leaves is illegal behaviour. -/
theorem oob_free_illegal : solo arena_oob_free = some (.error .illegal) := by
  decide +kernel

end AllocArena.ArenaObstruction
