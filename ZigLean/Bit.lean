import ZigLean.Basic

/-!
# Integer bit counts and left-shift overflow

Counts inspect the two's-complement bit pattern regardless of signedness. `m` is the
AIR result width (checked by `Air2Lean.Check`); zero returns the operand width for both
zero counts. Vectors lift these scalar definitions independently per lane.
-/

namespace Zig

@[inline] def clz {n : Nat} (m : Nat) (a : BitVec n) : BitVec m := a.clz.setWidth m
@[inline] def ctz {n : Nat} (m : Nat) (a : BitVec n) : BitVec m := a.ctz.setWidth m
@[inline] def popcount {n : Nat} (m : Nat) (a : BitVec n) : BitVec m := a.cpop.setWidth m

/-- `@shlWithOverflow`: wrapped bits and a flag when shifting back cannot recover the
operand. Signed operands shift back arithmetically, so losing a sign bit counts as overflow. -/
@[inline] def shlWithOverflow {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m) :
    Result (BitVec n × BitVec 1) :=
  if b.toNat < n ∨ b.toNat = 0 then
    let r := shl a b
    pure (r, if shr s r b = a then 0 else 1)
  else throw .illegal

private theorem resize_width_count (n m : Nat) :
    (BitVec.ofNat n n).setWidth m = BitVec.ofNat m n := by
  rcases Nat.le_total m n with h | h
  · exact BitVec.setWidth_ofNat_of_le h n
  · exact BitVec.setWidth_ofNat_of_le_of_lt h (Nat.lt_two_pow_self (n := n))

@[simp] theorem clz_zero (n m : Nat) : clz m (0 : BitVec n) = BitVec.ofNat m n := by
  unfold clz
  rw [(BitVec.clz_eq_iff_eq_zero (x := (0 : BitVec n))).mpr rfl]
  exact resize_width_count n m

@[simp] theorem ctz_zero (n m : Nat) : ctz m (0 : BitVec n) = BitVec.ofNat m n := by
  have hr : (0 : BitVec n).reverse = 0 := BitVec.reverse_eq_zero_iff.mpr rfl
  unfold ctz BitVec.ctz
  rw [hr]
  exact clz_zero n m

@[simp] theorem popcount_zero (n m : Nat) : popcount m (0 : BitVec n) = 0 := by
  simp [popcount]

/-- A resized count retains the upstream bitvector count exactly. -/
theorem clz_toNat {n : Nat} (m : Nat) (a : BitVec n) (h : a.clz.toNat < 2 ^ m) :
    (clz m a).toNat = a.clz.toNat := by
  simpa [clz, BitVec.toNat_setWidth] using Nat.mod_eq_of_lt h

theorem ctz_toNat {n : Nat} (m : Nat) (a : BitVec n) (h : a.ctz.toNat < 2 ^ m) :
    (ctz m a).toNat = a.ctz.toNat := by
  simpa [ctz, BitVec.toNat_setWidth] using Nat.mod_eq_of_lt h

theorem popcount_toNat {n : Nat} (m : Nat) (a : BitVec n) (h : a.cpop.toNat < 2 ^ m) :
    (popcount m a).toNat = a.cpop.toNat := by
  simpa [popcount, BitVec.toNat_setWidth] using Nat.mod_eq_of_lt h

@[simp] theorem popcount_allOnes (n m : Nat) :
    popcount m (BitVec.allOnes n) = BitVec.ofNat m n := by
  unfold popcount
  rw [BitVec.cpop_allOnes]
  exact resize_width_count n m

/-- The result width can hold every possible population count. -/
theorem popcount_le {n : Nat} (m : Nat) (a : BitVec n) (h : n < 2 ^ m) :
    (popcount m a).toNat ≤ n := by
  have hb := BitVec.toNat_cpop_le a
  rw [popcount_toNat m a (by omega)]
  exact hb

/-- A bitset has no set bit below the returned trailing-zero count. -/
theorem getLsbD_below_ctz {n : Nat} (m : Nat) (a : BitVec n)
    (h : a.ctz.toNat < 2 ^ m) (i : Nat) (hi : i < (ctz m a).toNat) :
    a.getLsbD i = false := by
  apply BitVec.getLsbD_false_of_lt_ctz
  simpa only [ctz_toNat m a h] using hi

/-- For a nonempty bitset the returned trailing-zero count names its lowest set bit. -/
theorem getLsbD_at_ctz {n : Nat} (m : Nat) (a : BitVec n)
    (h : a.ctz.toNat < 2 ^ m) (hne : a ≠ 0) :
    a.getLsbD (ctz m a).toNat = true := by
  rw [ctz_toNat m a h]
  exact BitVec.getLsbD_true_ctz_of_ne_zero hne

theorem shlWithOverflow_result {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (hb : b.toNat < n) : shlWithOverflow s a b =
      pure (shl a b, if shr s (shl a b) b = a then 0 else 1) := by
  simp [shlWithOverflow, hb]

theorem shlWithOverflow_noOverflow {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (hb : b.toNat < n) (h : shr s (shl a b) b = a) :
    shlWithOverflow s a b = pure (shl a b, 0) := by
  simp [shlWithOverflow, hb, h]

theorem shlWithOverflow_overflow {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (hb : b.toNat < n) (h : shr s (shl a b) b ≠ a) :
    shlWithOverflow s a b = pure (shl a b, 1) := by
  simp [shlWithOverflow, hb, h]

/-- A representable Log2Int count can still be invalid for a non-power-of-two width. -/
theorem shlWithOverflow_illegal {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (hwidth : n ≤ b.toNat) (hpositive : b.toNat ≠ 0) :
    shlWithOverflow s a b = throw .illegal := by
  simp [shlWithOverflow, Nat.not_lt_of_le hwidth, hpositive]

/-- Clients can move between the explicit overflow flag and the existing checked shift. -/
theorem shlExact_of_noOverflow {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (h : shr s (shl a b) b = a) : shlExact s a b = pure (shl a b) := by
  have h' : shr s (a <<< b.toNat) b = a := by simpa only [shl] using h
  simp [shlExact, shl, h']

end Zig
