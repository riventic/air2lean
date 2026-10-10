import ZigLean.Lemmas

/-!
# Arithmetic ranges and BitVec/Int/Nat conversions

Conditional rewrite lemmas that move fixed-width arithmetic to `Nat`/`Int` once a range
premise holds, and range bounds for sums of fixed-width values. Every lemma is an ordinary
kernel-checked theorem (no compiled decision procedure, no evaluation of large numerals). The
premises are ordinary hypotheses, discharged by `omega` or `assumption` in `zig_range`.

`zig_range` rewrites with these lemmas and the unsigned lemmas of `ZigLean.Lemmas`, trying to
discharge each range premise from the context; a premise it cannot prove leaves the original
term in place, so the remaining range obligation stays visible in the goal.
-/

namespace Zig

variable {n m : Nat}

/-! ## BitVec ↔ Nat -/

theorem toNat_add_of_lt {a b : BitVec n} (h : a.toNat + b.toNat < 2 ^ n) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_sub_of_le {a b : BitVec n} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt
  rw [BitVec.toNat_sub, show 2 ^ n - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ n by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_mul_of_lt {a b : BitVec n} (h : a.toNat * b.toNat < 2 ^ n) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h

theorem toNat_setWidth_of_le {a : BitVec n} (h : n ≤ m) : (a.setWidth m).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) h))

theorem toNat_setWidth_of_lt {a : BitVec n} (h : a.toNat < 2 ^ m) :
    (a.setWidth m).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_of_lt {k : Nat} (h : k < 2 ^ n) : (BitVec.ofNat n k).toNat = k := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## BitVec ↔ Int -/

/-- A value below the sign bit has the same signed and unsigned reading. -/
theorem toInt_of_lt {a : BitVec n} (h : 2 * a.toNat < 2 ^ n) : a.toInt = (a.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; simp [h]

theorem toNat_ofInt_natCast {k : Nat} (h : k < 2 ^ n) :
    (BitVec.ofInt n (k : Int)).toNat = k := by
  rw [BitVec.ofInt_natCast]; exact toNat_ofNat_of_lt h

/-! ## Checked arithmetic that cannot fail in range -/

theorem add_unsigned_of_lt {a b : BitVec n} (h : a.toNat + b.toNat < 2 ^ n) :
    add false a b = pure (a + b) := by
  rw [add_unsigned]; simp [Nat.not_le.mpr h]

theorem sub_unsigned_of_le {a b : BitVec n} (h : b.toNat ≤ a.toNat) :
    sub false a b = pure (a - b) := by
  rw [sub_unsigned]; simp [Nat.not_lt.mpr h]

theorem mul_unsigned_of_lt {a b : BitVec n} (h : a.toNat * b.toNat < 2 ^ n) :
    mul false a b = pure (a * b) := by
  rw [mul_unsigned]; simp [Nat.not_le.mpr h]

/-- A saturating unsigned subtraction is the truncated one. -/
theorem subSat_unsigned_toNat (a b : BitVec 64) : (subSat false a b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [subSat, clamp, val, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.toNat_ofInt]
  have h64 : ((2 : Int) ^ 64) = 18446744073709551616 := by rfl
  have h64' : (2 : Nat) ^ 64 = 18446744073709551616 := by rfl
  simp only [h64, h64'] at *
  omega

/-- An unsigned narrowing `@intCast` succeeds exactly when the value fits. -/
theorem intCast_unsigned_of_lt {a : BitVec n} (h : a.toNat < 2 ^ m) :
    intCast false false m a = pure (BitVec.ofNat m a.toNat) := by
  have hfit : (a.toNat : Int) ≤ 2 ^ m - 1 := by
    have : ((2 ^ m : Nat) : Int) = 2 ^ m := by norm_cast
    omega
  simp only [intCast, val, Bool.false_eq_true, ↓reduceIte, Int.natCast_nonneg, hfit, and_self]
  rw [BitVec.ofInt_natCast]

/-! ## Range bounds -/

theorem sum_map_le_mul {α : Type} (l : List α) (f : α → Nat) (B : Nat) (h : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

/-- The sum of `k` values of width `w` is at most `k * (2 ^ w - 1)`. -/
theorem sum_toNat_le {w : Nat} (l : List (BitVec w)) :
    (l.map BitVec.toNat).sum ≤ l.length * (2 ^ w - 1) :=
  sum_map_le_mul l _ _ fun x _ => Nat.le_sub_one_of_lt x.isLt

/-- A sum of at most `2 ^ k` values of width `w` fits in width `w + k`. -/
theorem sum_toNat_lt {w k : Nat} (l : List (BitVec w)) (h : l.length ≤ 2 ^ k) :
    (l.map BitVec.toNat).sum < 2 ^ (w + k) := by
  have hw : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos
  calc (l.map BitVec.toNat).sum ≤ l.length * (2 ^ w - 1) := sum_toNat_le l
    _ ≤ 2 ^ k * (2 ^ w - 1) := Nat.mul_le_mul_right _ h
    _ < 2 ^ k * 2 ^ w := Nat.mul_lt_mul_of_pos_left hw (Nat.two_pow_pos k)
    _ = 2 ^ (w + k) := by rw [Nat.pow_add, Nat.mul_comm]

end Zig

/-- Rewrite fixed-width arithmetic to `Nat`/`Int` where each range premise follows from the
context by `omega` or `assumption`; undischarged premises leave the term unchanged. -/
macro "zig_range" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := first | assumption | omega) only [Zig.toNat_add_of_lt,
    Zig.toNat_sub_of_le, Zig.toNat_mul_of_lt, Zig.toNat_setWidth_of_le, Zig.toNat_setWidth_of_lt,
    Zig.toNat_ofNat_of_lt, Zig.toInt_of_lt, Zig.toNat_ofInt_natCast, Zig.add_unsigned_of_lt,
    Zig.sub_unsigned_of_le, Zig.mul_unsigned_of_lt, Zig.intCast_unsigned_widen,
    Zig.intCast_unsigned_of_lt] $[$loc]?)
