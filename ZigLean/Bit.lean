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

/-! ## Arbitrary widths

The lemmas below are uniform in the operand width, so they cover u128/i128, non-power-of-two
widths such as u24/u40/i7, and every lane of a vector. Concrete wide/narrow instances are
kernel-checked in `tests/roadmap/bitops/Runtime.lean`. -/

/-- The checker's count width `log2 n + 1` can hold every count of an `n`-bit operand. -/
theorem countWidth_holds (n : Nat) : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self

theorem clz_le_width {n : Nat} (a : BitVec n) : a.clz.toNat ≤ n := by
  have h := BitVec.le_def.mp (BitVec.clz_le (x := a))
  simpa [Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := n))] using h

theorem ctz_le_width {n : Nat} (a : BitVec n) : a.ctz.toNat ≤ n := by
  rw [BitVec.ctz_eq_reverse_clz]
  exact clz_le_width a.reverse

/-- With a result width that can hold the source width, every count is exact. -/
theorem clz_toNat_of_width {n m : Nat} (a : BitVec n) (h : n < 2 ^ m) :
    (clz m a).toNat = a.clz.toNat :=
  clz_toNat m a (Nat.lt_of_le_of_lt (clz_le_width a) h)

theorem ctz_toNat_of_width {n m : Nat} (a : BitVec n) (h : n < 2 ^ m) :
    (ctz m a).toNat = a.ctz.toNat :=
  ctz_toNat m a (Nat.lt_of_le_of_lt (ctz_le_width a) h)

theorem popcount_toNat_of_width {n m : Nat} (a : BitVec n) (h : n < 2 ^ m) :
    (popcount m a).toNat = a.cpop.toNat :=
  popcount_toNat m a (Nat.lt_of_le_of_lt (BitVec.toNat_cpop_le a) h)

/-- Signed/unsigned boundary: a set top bit (every negative signed value, and every unsigned
value at or above `2^(n-1)`) has no leading zeros. -/
theorem clz_of_msb {n : Nat} (m : Nat) (a : BitVec n) (h : a.msb = true) :
    clz m a = 0 := by
  have hn : 0 < n := by
    rcases n with _ | n
    · have hlt := a.isLt
      simp [BitVec.msb_eq_decide] at h hlt
      omega
    · omega
  have hz : a.clz.toNat = 0 :=
    (BitVec.clz_eq_zero_iff hn).mpr (by simpa [BitVec.msb_eq_decide] using h)
  apply BitVec.eq_of_toNat_eq
  simp [clz, BitVec.toNat_setWidth, hz]

@[simp] theorem clz_allOnes {n : Nat} (m : Nat) (hn : 0 < n) : clz m (BitVec.allOnes n) = 0 :=
  clz_of_msb m _ (by simp [BitVec.msb_allOnes hn])

@[simp] theorem ctz_allOnes {n : Nat} (m : Nat) (hn : 0 < n) : ctz m (BitVec.allOnes n) = 0 := by
  have hr : (BitVec.allOnes n).reverse = BitVec.allOnes n := by
    ext i hi; simp [BitVec.getElem_reverse, hi]
  unfold ctz BitVec.ctz
  rw [hr]
  exact clz_allOnes m hn

/-- A count of the operand's width is valid exactly when it is zero or below the width;
`Log2Int` counts of a power-of-two width are therefore always valid. -/
theorem shlWithOverflow_valid {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (hb : b.toNat < n ∨ b.toNat = 0) :
    shlWithOverflow s a b = pure (shl a b, if shr s (shl a b) b = a then 0 else 1) := by
  simp [shlWithOverflow, hb]

theorem shlWithOverflow_pow2 {k : Nat} (s : Bool) (a : BitVec (2 ^ k)) (b : BitVec k) :
    shlWithOverflow s a b = pure (shl a b, if shr s (shl a b) b = a then 0 else 1) :=
  shlWithOverflow_valid s a b (.inl (Nat.lt_of_lt_of_le b.isLt (Nat.le_refl _)))

/-- A zero count preserves the operand and never overflows, at every width. -/
@[simp] theorem shlWithOverflow_zero_count {n m : Nat} (s : Bool) (a : BitVec n) :
    shlWithOverflow s a (0 : BitVec m) = pure (a, 0) := by
  cases s <;> simp [shlWithOverflow, shl, shr]

/-- A zero operand never loses bits under a valid count. -/
theorem shlWithOverflow_zero_operand {n m : Nat} (s : Bool) (b : BitVec m)
    (hb : b.toNat < n ∨ b.toNat = 0) :
    shlWithOverflow s (0 : BitVec n) b = pure (0, 0) := by
  cases s <;> simp [shlWithOverflow, shl, shr, hb, BitVec.zero_shiftLeft, BitVec.zero_ushiftRight]

/-- Bitset iteration (`x & (x -% 1)`, removing the lowest member) strictly decreases a
nonempty word at every width: the iterator's termination measure. -/
theorem and_subWrap_one_lt {n : Nat} (x : BitVec n) (hx : x ≠ 0) :
    (x &&& subWrap x 1).toNat < x.toNat := by
  have hpos : 0 < x.toNat := by
    rcases Nat.eq_zero_or_pos x.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hx
    · exact h
  have hn : n ≠ 0 := by
    rintro rfl
    exact hx (Subsingleton.elim x 0)
  have h1 : (1 : BitVec n).toNat = 1 := by
    simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hn)]
  have hlt := x.isLt
  have hsub : (subWrap x 1).toNat = x.toNat - 1 := by
    simp only [subWrap, BitVec.toNat_sub, h1]
    rw [show 2 ^ n - 1 + x.toNat = (x.toNat - 1) + 2 ^ n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

/-- Clients can move between the explicit overflow flag and the existing checked shift. -/
theorem shlExact_of_noOverflow {n m : Nat} (s : Bool) (a : BitVec n) (b : BitVec m)
    (h : shr s (shl a b) b = a) : shlExact s a b = pure (shl a b) := by
  have h' : shr s (a <<< b.toNat) b = a := by simpa only [shl] using h
  simp [shlExact, shl, h']

end Zig
