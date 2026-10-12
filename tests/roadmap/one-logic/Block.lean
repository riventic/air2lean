import ZigLean.Sep.Full.AutoAll

/-!
# Blocks in the full-state logic (`ZigLean/Sep/Full/Block.lean`), library-only

A block is made and ended again; `fsym` walks it with the library's `alloc` and `free` rules
(partial: `alloc` may find no room, a stack overflow).
-/

namespace OneLogic.Block

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Make an 8-byte heap block and free it. -/
def cycle : MemM Unit := do
  let p ← Zig.alloc .heap 8 8
  Zig.free p

theorem cycle_spec (R : FAssn) : FTriple R cycle (fun _ => R) := by
  unfold cycle
  fsym

/-- The same with a stack block (`allocStack`). -/
def stackCycle : MemM Unit := do
  let p ← Zig.allocStack 16 8
  Zig.free p

theorem stackCycle_spec (R : FAssn) : FTriple R stackCycle (fun _ => R) := by
  unfold stackCycle
  fsym

end OneLogic.Block
