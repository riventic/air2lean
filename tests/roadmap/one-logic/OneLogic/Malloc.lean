import ZigLean.Sep.Full.AutoAll

/-!
# macOS `malloc`/`free` in the full-state logic (`ZigLean/Sep/Full/Malloc.lean`), library-only

A `malloc` block is written and freed again; `fsym` walks it with the library's `malloc`, `store`
and `free` rules. Total: `malloc` finds no room as `null`, never as a stack overflow.
-/

namespace OneLogic.Malloc

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Allocate 8 bytes, store into the last byte, free the block; `null` does nothing. -/
def cycle (env : Os.Env) : MemM Unit := do
  match ← Os.Darwin.malloc env 8 with
  | some p =>
    store 1 (p.add 7) (1 : BitVec 8)
    Os.Darwin.free (some p)
  | none => pure ()

theorem cycle_spec (env : Os.Env) (R : FAssn) : FTotalTriple R (cycle env) (fun _ => R) := by
  unfold cycle
  fsym

/-- `free(null)` does nothing. -/
theorem freeNull_spec (R : FAssn) : FTotalTriple R (Os.Darwin.free none) (fun _ => R) := by
  fsym

end OneLogic.Malloc
