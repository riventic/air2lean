import Proofs.Basic.Gen

/-!
# Shared definitions for the `basic` proofs

`psum xs k` is the sum of the first `k` elements as a natural number, with its bounds.
-/

/-- Sum of the first `k` elements, as a natural number. -/
def psum (xs : Array (BitVec 32)) (k : Nat) : Nat := ((xs.toList.take k).map BitVec.toNat).sum

theorem list_sum_le (l : List (BitVec 32)) : (l.map BitVec.toNat).sum ≤ l.length * 2 ^ 32 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have := x.isLt
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]; omega

theorem psum_le (xs : Array (BitVec 32)) (k : Nat) : psum xs k ≤ k * 2 ^ 32 := by
  unfold psum
  have h := list_sum_le (xs.toList.take k)
  have : (xs.toList.take k).length ≤ k := by simp [Nat.min_le_left]
  exact Nat.le_trans h (Nat.mul_le_mul_right _ this)

theorem psum_succ (xs : Array (BitVec 32)) (k : Nat) (hk : k < xs.size) :
    psum xs (k + 1) = psum xs k + xs[k].toNat := by
  unfold psum
  rw [Zig.sum_take_succ _ _ _ (by simpa using hk)]; simp
