import ZigLean.Basic

/-!
# Lemmas for proofs about generated code

Unsigned forms, stated with `toNat`, so goals reduce to `omega`.
-/

namespace Zig

variable {n : Nat} {safe : Bool}

/-- The checked (`_safe`) form's error is its panic, the plain form's `.illegal`. -/
@[simp] theorem Error.ifSafe_true (e : Error) : Error.ifSafe true e = e := rfl
@[simp] theorem Error.ifSafe_false (e : Error) : Error.ifSafe false e = .illegal := rfl

@[simp] theorem add_unsigned (a b : BitVec n) :
    add false a b safe =
      if a.toNat + b.toNat ≥ 2 ^ n then throw (.ifSafe safe .overflow) else pure (a + b) := by
  simp [add, BitVec.uaddOverflow]

@[simp] theorem sub_unsigned (a b : BitVec n) :
    sub false a b safe = if a.toNat < b.toNat then throw (.ifSafe safe .overflow) else pure (a - b) := by
  simp [sub, BitVec.usubOverflow]

@[simp] theorem mul_unsigned (a b : BitVec n) :
    mul false a b safe =
      if a.toNat * b.toNat ≥ 2 ^ n then throw (.ifSafe safe .overflow) else pure (a * b) := by
  simp [mul, BitVec.umulOverflow]

/-- Unsigned widening never fails. -/
@[simp] theorem intCast_unsigned_widen (a : BitVec n) (m : Nat) (h : n ≤ m) :
    intCast false false m a safe = pure (a.setWidth m) := by
  have ha := a.isLt
  have hp : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) h
  have hfit : (a.toNat : Int) ≤ 2 ^ m - 1 := by
    have : ((2 ^ m : Nat) : Int) = 2 ^ m := by norm_cast
    omega
  simp only [intCast, intLo_unsigned, intHi_unsigned, val, Bool.false_eq_true, ↓reduceIte]
  simp only [Int.natCast_nonneg, hfit, and_self, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

@[simp] theorem lt_unsigned (a b : BitVec n) : lt false a b = decide (a.toNat < b.toNat) := by
  simp [lt, BitVec.ult]

@[simp] theorem gt_unsigned (a b : BitVec n) : gt false a b = decide (b.toNat < a.toNat) := by
  simp [gt, lt, BitVec.ult]

@[simp] theorem index_lt {α : Type} (a : Array α) (i : usize) (h : i.toNat < a.size) :
    index a i = pure a[i.toNat] := by
  simp [index, h]

/-- A loop counter's `+ 1` that does not wrap. -/
theorem toNat_add_one (x : BitVec n) (h : x.toNat + 1 < 2 ^ n) : (x + 1).toNat = x.toNat + 1 := by
  have h1 : (1 : BitVec n).toNat = 1 := by
    show (BitVec.ofNat n 1).toNat = 1; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, h1]; exact Nat.mod_eq_of_lt h

/-- A recursion argument's `- 1` from a nonzero value. -/
theorem toNat_sub_one (x : BitVec n) (h : x ≠ 0#n) : (x - 1#n).toNat = x.toNat - 1 := by
  have hx : x.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hlt := x.isLt
  have h1 : (1#n).toNat = 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub, h1]
  rw [show 2 ^ n - 1 + x.toNat = (x.toNat - 1) + 2 ^ n by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- One step of a prefix sum over `l.take k` (the loop invariants of `sum`-like loops). -/
theorem sum_take_succ {α : Type} (l : List α) (f : α → Nat) (k : Nat) (hk : k < l.length) :
    ((l.take (k + 1)).map f).sum = ((l.take k).map f).sum + f l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append,
    List.sum_append]
  simp

/-! ## Integer ranges at every width, including the zero-bit `i0`/`u0`

`intLo`/`intHi` are the one range definition (`clamp`, `intCast`, `@intFromFloat`). The `i0`
regression (`docs/architecture-audit/zero-width-ints.md`): with Nat subtraction, `-(2^(m-1))` at
`m = 0` was `-1`, so `@intCast` to `i0` accepted -1. -/

/-- Every value of an `n`-bit type lies in its range, for every `n` (including 0). -/
theorem val_mem_range (s : Bool) (a : BitVec n) : intLo s n ≤ val s a ∧ val s a ≤ intHi s n := by
  cases n with
  | zero => cases s <;> simp [val, BitVec.toInt_zero_length, BitVec.of_length_zero]
  | succ k =>
    have h3 : (a.toNat : Int) < 2 ^ (k + 1) := by exact_mod_cast a.isLt
    have h4 : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by rw [Int.pow_succ]; omega
    cases s
    · simp only [val, Bool.false_eq_true, ↓reduceIte, intLo_unsigned, intHi_unsigned]
      omega
    · have h1 := BitVec.le_toInt a
      have h2 := BitVec.toInt_lt (x := a)
      simp only [val, ↓reduceIte, intLo_signed_succ, intHi_signed_succ, Nat.add_sub_cancel] at *
      omega

/-- An in-range integer is recovered exactly by `BitVec.ofInt`, at every width (including 0). -/
theorem val_ofInt_of_range (s : Bool) {v : Int} (h : intLo s n ≤ v ∧ v ≤ intHi s n) :
    val s (BitVec.ofInt n v) = v := by
  cases n with
  | zero =>
    have : v = 0 := by simp at h; omega
    subst this
    cases s <;> simp [val, BitVec.toInt_zero_length, BitVec.of_length_zero]
  | succ k =>
    have h4 : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by rw [Int.pow_succ]; omega
    cases s
    · simp only [intLo_unsigned, intHi_unsigned] at h
      simp only [val, Bool.false_eq_true, ↓reduceIte]
      have h5 : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ (k + 1) := by norm_cast
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h.1 (by omega)]
      omega
    · simp only [intLo_signed_succ, intHi_signed_succ] at h
      simp only [val, ↓reduceIte]
      exact BitVec.toInt_ofInt_eq_self (Nat.succ_pos k) (by simpa using h.1) (by simpa using (by omega : v < 2 ^ k))

/-- The range of every type is nonempty, at every width. -/
theorem intLo_le_intHi (s : Bool) (n : Nat) : intLo s n ≤ intHi s n := by
  cases n with
  | zero => simp
  | succ k =>
    have : (0 : Int) < 2 ^ k := by exact_mod_cast Nat.two_pow_pos k
    cases s <;> simp <;> omega

/-- `clamp` lands in the range and equals the mathematical clamp, at every width. -/
theorem val_clamp (s : Bool) (n : Nat) (v : Int) :
    val s (clamp s n v) = Max.max (intLo s n) (Min.min (intHi s n) v) := by
  apply val_ofInt_of_range
  have := intLo_le_intHi s n
  omega

/-- A successful `@intCast` preserves the mathematical value, at every width. With the old `-1`
bound at `m = 0`, `-1` was "cast" to `0`. -/
theorem intCast_val (s₁ s₂ : Bool) (m : Nat) (a : BitVec n) (r : BitVec m)
    (h : intCast s₁ s₂ m a = pure r) : val s₂ r = val s₁ a := by
  unfold intCast at h
  by_cases hr : intLo s₂ m ≤ val s₁ a ∧ val s₁ a ≤ intHi s₂ m
  · simp only [hr, and_self, ↓reduceIte] at h
    have : BitVec.ofInt m (val s₁ a) = r := by
      have h' : (some (Except.ok (BitVec.ofInt m (val s₁ a))) : Option (Except Error (BitVec m))) =
          some (Except.ok r) := h
      simpa using h'
    subst this
    exact val_ofInt_of_range s₂ hr
  · simp only [hr, ↓reduceIte] at h
    have h' : (some (Except.error Error.overflow) : Option (Except Error (BitVec m))) =
          some (Except.ok r) := h
    simp at h'

/-- `@intCast` to `i0` rejects -1 (an `i8` value) as native Zig does. -/
theorem intCast_i0_rejects_neg_one :
    intCast true true 0 (BitVec.ofInt 8 (-1)) = (throw .overflow : Result (BitVec 0)) := by
  rfl

/-- `@intCast` to `i0` and `u0` accepts 0 and rejects 1. -/
theorem intCast_zero_width_range (s : Bool) :
    intCast s s 0 (0 : BitVec 8) = (pure 0 : Result (BitVec 0)) ∧
    intCast s s 0 (1 : BitVec 8) = (throw .overflow : Result (BitVec 0)) := by
  cases s <;> constructor <;> rfl

end Zig
