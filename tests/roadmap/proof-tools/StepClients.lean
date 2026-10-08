import ZigLean.Sep.Step
import Proofs.Slices.Gen

/-!
The two generated array clients of `ArrayClients.lean` and their composition, proved again
with the symbolic-execution tactics of `ZigLean.Sep.Step`. The statements are exactly those
of `generated_at_array`, `generated_bumpAt_array` and the composition example there; the
manual proofs in `ArrayClients.lean` stay as the evidence for the reassembly interface.
`sep_unfold` normalizes the generated `MM` body, `sep_steps` executes the indexed loads and
the store against `arr p xs` with the frame inferred, and `sep_ret` closes the postcondition.
-/

open Zig Assn

theorem at_array_steps (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64)
    (hi : i.toNat < xs.length) (R : Assn) :
    Triple (arr p xs ∗ R) (Slices.«at» p i)
      (fun v => (⌜v = xs[i.toNat]⌝ ∗ arr p xs) ∗ R) := by
  sep_unfold [Slices.«at»]
  sep_steps
  sep_ret

theorem bumpAt_array_steps (p : Ptr) (xs : List (BitVec 8)) (i : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (R : Assn) :
    Triple (arr p xs ∗ R) (Slices.bumpAt p i)
      (fun v => (⌜v = (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))[3]'(by simp only [List.length_set]; omega)⌝ ∗
        arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) ∗ R) := by
  sep_unfold [Slices.bumpAt, show i.toNat < 4 by omega]
  sep_steps
  sep_ret

-- The composition uses the two contracts as `sep_step using` rules; the frame of each call
-- (the other array) is inferred.
example (p q : Ptr) (xs : List (BitVec 8)) (ys : List (BitVec 32)) (i j : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (hj : j.toNat < ys.length) :
    Triple (arr p xs ∗ arr q ys)
      (Slices.bumpAt p i >>= fun _ => Slices.«at» q j)
      (fun v => (⌜v = ys[j.toNat]⌝ ∗ arr q ys) ∗
        arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) := by
  sep_step using bumpAt_array_steps p xs i hlen hi (arr q ys)
  sep_step using at_array_steps q ys j hj _
  sep_ret

/-- info: 'bumpAt_array_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bumpAt_array_steps
