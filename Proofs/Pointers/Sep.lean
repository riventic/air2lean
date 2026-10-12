import Proofs.Pointers.Gen
import ZigLean.Sep.Full.AutoAll

/-!
# Separation-logic proofs about `examples/pointers/pointers.zig`

`swap` exchanges the values of two `u32` that do not overlap (`pts p 4 x ⋆ pts q 4 y`), and
`swap(p, p)` keeps the value. The rest of the memory is unchanged. Both are total: the run
returns. `fsym` walks the generated code with the library's load and store rules; the strength
log (`tests/roadmap/strength-log/ProofsPointers.lean`) gives back the legacy statements.
-/

open Pointers Zig Zig.Full FAssn

theorem swap_sep (p q : Ptr) (x y : BitVec 32) :
    FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (swap p q)
      (fun _ => up (pts p 4 y) ⋆ up (pts q 4 x)) := by
  fsym

/-- `swap(p, p)` keeps the value. -/
theorem swap_self_sep (p : Ptr) (x : BitVec 32) :
    FTotalTriple (up (pts p 4 x)) (swap p p) (fun _ => up (pts p 4 x)) := by
  fsym

/-! ## Non-vacuity witnesses: two `u32` one after the other in one block -/

/-- `0` at `p0` and `1` at `p0 + 4`. -/
theorem swap_pre : Witness.FAdmit (up (pts Witness.p0 4 (0 : BitVec 32)) ⋆
    up (pts (Witness.p0.add 4) 4 (1 : BitVec 32))) :=
  (Witness.FAdmit.up (Witness.mem1_pts₂ (0 : BitVec 32) (1 : BitVec 32) (by decide) (by decide +kernel))
    (Witness.mem1_fseq _ _ (by decide +kernel))).mono fun _ h => up_sep h

theorem swap_self_pre : Witness.FAdmit (up (pts Witness.p0 4 (0 : BitVec 32))) :=
  Witness.FAdmit.up Witness.pts32 (Witness.mem1_fseq _ _ (by decide +kernel))

-- Total triples: the return is part of the claim, so they need no liveness witness.
nonvacuity_witness swap_sep := ⟨Witness.p0, Witness.p0.add 4, 0, 1, swap_pre⟩
nonvacuity_witness swap_self_sep := ⟨Witness.p0, 0, swap_self_pre⟩
