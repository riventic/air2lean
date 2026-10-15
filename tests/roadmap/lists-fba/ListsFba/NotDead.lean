import ListsFba.Witness

/-!
# A `FixedBufferAllocator` free does not end a block (`dead` regression)

`dead b` (`ZigLean/Sep/Full/Res.lean`, `KFact.dead`) is knowledge that block `b` is dead. Only
the steps that end a block give it (`FTotalTriple.free_dead`, `FTotalTriple.munmapWhole_dead`);
the allocator contract (`FAllocSpec`, `CAllocSpec`) does not promise it, because an allocator's
`free` need not end a block. This file shows it for the translated `FixedBufferAllocator`: from
the program-start memory of `ListsFba.Witness` (`gs`: the allocator struct and its 16-byte
buffer, block 1), `alloc(16)` then `free` of the grant returns, and the buffer's block is still
live (`free_keeps_block`, the kernel runs the translated code). So no resource that memory holds
contains `dead 1` (`free_not_dead`, from `Holds.dead`): a client of this allocator cannot learn
that a freed grant's block is dead, and the contract must not say so.
-/

namespace ListsFba.NotDead

open Zig Zig.Full Zig.Full.FAssn

/-- `alloc(16)` at alignment `2 ^ 3`, then `free` of the grant; whether the grant was in the
buffer's block (1). -/
def allocFree : MemM Bool := do
  match ← AllocFba.impl.alloc ctx 16 3 0 with
  | some q => do AllocFba.impl.free ctx ⟨q, 16⟩ 3 0; pure (q.block == some 1)
  | none => pure false

/-- The program-start memory (any placement: `Placement.fresh`). -/
def m0 : Mem := Mem.ofGlobals Placement.fresh gs

/-- The memory after `allocFree`, if it returns. -/
def mAfter : Option Mem := match (allocFree.run m0).run with
  | some (.ok (_, m)) => some m
  | _ => none

/-- `alloc` grants 16 bytes of the buffer's block (1), `free` gives them back and returns, and the
block is live afterwards. -/
theorem free_keeps_block :
    (match (allocFree.run m0).run with
      | some (.ok (inBuf, m)) => inBuf && (m.blocks[1]?.map (·.live)) == some true
      | _ => false) = true := by
  decide +kernel

/-- **No resource held after the `free` knows the buffer's block dead.** -/
theorem free_not_dead {m : Mem} (hm : mAfter = some m) {r rF : Res} {R : FAssn}
    (hh : Holds m r rF) : ¬ (dead 1 ⋆ R) r := fun h => by
  obtain ⟨blk, hb, hl⟩ := hh.dead h
  have := free_keeps_block
  unfold mAfter at hm
  split at hm <;> rename_i e <;> simp only [e] at this hm
  · cases hm; simp [hb, hl] at this
  · cases hm

end ListsFba.NotDead
