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
in its current generation. Owned bytes and duplicable block knowledge cannot say that; the
ghost epoch ledgers of `ZigLean/Sep/Full/Ghost.lean` can: `ArenaSpec.lean`'s token is a ghost token
of the current epoch that names the region, which shows that the arena granted it and so has a
node (`ArenaSpec.free_pre`).

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
  ((Sched.run Sched.soloEnv dispatch 100000 (fun _ => 0) main (mem0 .fresh)).run).map fun r => r.map (·.1)

/-- **O-A.** Freeing a foreign slice through a fresh arena panics. -/
theorem foreign_free_panics : solo arena_foreign_free = some (.error .panic) := by
  decide +kernel

/-- **O-E.** `free` in the state that a failed `alloc` leaves is illegal behaviour. -/
theorem oob_free_illegal : solo arena_oob_free = some (.error .illegal) := by
  decide +kernel

/-- The program's memory at start. -/
def mem00 : Mem := mem0 .fresh

/-- A live 32-byte block at `2^64 - 32`. -/
def topBlock : Block :=
  { bytes := Array.replicate 32 .undef, align := 8, kind := .heap, live := true, addr := 2 ^ 64 - 32 }

/-- A memory whose last block (32 bytes, a node's header and 8 buffer bytes) ends at `2^64`: the
model's placement admits it (`Mem.placeOk`: `A + size ≤ 2^64`), no native process has it. -/
def memTop : Mem := { mem00 with blocks := mem00.blocks.push topBlock }

/-- The run ends in `.overflow`. -/
def overflows {α : Type} : Option (Except Error α) → Bool
  | some (.error .overflow) => true
  | _ => false

/-- **O-H** (old behaviour, to become unreachable): `alignedIndex(buf.ptr, end_index, .@"8")`,
which `alloc`'s fast path calls after the reservation check, with the buffer ending at `2^64` and
`end_index = 5`: `Alignment.forward` adds `7` to `2^64 - 3` with an overflow check. -/
theorem aligned_index_overflows :
    overflows ((heap_ArenaAllocator_alignedIndex ⟨some mem00.blocks.size, 24⟩ 5 mem_Alignment.«8»).run
      memTop).run = true := by
  decide +kernel

-- `check.sh` requires only the standard axioms.
#print axioms foreign_free_panics
#print axioms oob_free_illegal
#print axioms aligned_index_overflows

end AllocArena.ArenaObstruction
