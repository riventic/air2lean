import ZigLean.Sep.Array.Reassemble
import ZigLean.Sep.Step
import Proofs.Slices.Gen

/-!
Two clients of the scalar array interface use the existing generated public
`examples/slices/slices.zig` bodies. No generated body is copied or hand-replaced.
These are sequential memory contracts; no new exporter/source correspondence
qualification is claimed by this fixture. The proofs execute the generated bodies with the
`sep_*` tactics of `ZigLean.Sep.Step`.
-/

open Zig Assn

-- The public generated pointer-index reader preserves its array and an independent frame.
theorem generated_at_array (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64)
    (hi : i.toNat < xs.length) (R : Assn) :
    Triple (arr p xs ∗ R) (Slices.«at» p i)
      (fun v => (⌜v = xs[i.toNat]⌝ ∗ arr p xs) ∗ R) := by
  sep_unfold [Slices.«at»]
  sep_steps
  sep_ret

-- The public generated fixed-capacity byte update reads a selected value, increments
-- modulo 256, stores through the shared interface, then returns element 3.
theorem generated_bumpAt_array (p : Ptr) (xs : List (BitVec 8)) (i : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (R : Assn) :
    Triple (arr p xs ∗ R) (Slices.bumpAt p i)
      (fun v => (⌜v = (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))[3]'(by simp only [List.length_set]; omega)⌝ ∗
        arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) ∗ R) := by
  sep_unfold [Slices.bumpAt, show i.toNat < 4 by omega]
  sep_steps
  sep_ret

-- The two clients can be called sequentially with unrelated allocated blocks.
example (p q : Ptr) (xs : List (BitVec 8)) (ys : List (BitVec 32)) (i j : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (hj : j.toNat < ys.length) :
    Triple (arr p xs ∗ arr q ys)
      (Slices.bumpAt p i >>= fun _ => Slices.«at» q j)
      (fun v => (⌜v = ys[j.toNat]⌝ ∗ arr q ys) ∗
        arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) := by
  sep_step using generated_bumpAt_array p xs i hlen hi (arr q ys)
  sep_step using generated_at_array q ys j hj _
  sep_ret
