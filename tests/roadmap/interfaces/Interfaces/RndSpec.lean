import Interfaces.Rnd
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region

/-!
# `rnd.zig` for every `std.Random` (`docs/interfaces.md`, the second interface)

The same mechanism as `std.mem.Allocator` (`Proofs/Lists/Alloc.lean`, `MixSpec`): the call through
`std.Random`'s `fillFn` is a `Table` of the program's fill functions (none here) with the
environment `env` (the generated `Ext.call0`, premise EXT-05), and `roll`'s theorem assumes the
library's `std.Random` contract (`FnSpec` with `randomFillPre`/`randomFillPost`) of the function
that the call runs, for any generator state `R`.
-/

namespace Interfaces.RndSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Rnd

variable [Ext]

/-- The environment's fill functions: `Ext.call0`. -/
def env : EnvFn Tgt (Ptr × Slice) Unit := fun f a => Ext.call0 f a.1 a.2

set_option maxHeartbeats 2000000 in
/-- **A die roll is 1 to 6, for every generator**: the fill function that `r` reaches meets
`std.Random`'s contract with its state `R`. -/
theorem roll_spec (r : Random) (R : FAssn)
    (h : ∀ A S K bs, FnSpec (randomFillPre r.ptr R A S K bs) (randomFillPost R A S K)
      (Table.callOr [] env r.fillFn)) :
    CTriple R (roll r) (fun v => ⟪1 ≤ v.toNat ∧ v.toNat ≤ 6⟫ ⋆ R) := by
  -- the program has no fill function: the call reaches the environment
  rw [show Table.callOr [] env r.fillFn = fun a => extCall (env r.fillFn a) from
    funext (Table.callOr_of_fresh (Table.fresh_nil _) env)] at h
  fsym [FnSpec.randomFill h]

end Interfaces.RndSpec
