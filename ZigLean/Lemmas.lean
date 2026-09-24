import ZigLean.Basic

/-!
# Lemmas for proofs about generated code

Unsigned forms, stated with `toNat`, so goals reduce to `omega`.
-/

namespace Zig

variable {n : Nat}

@[simp] theorem add_unsigned (a b : BitVec n) :
    add false a b = if a.toNat + b.toNat ≥ 2 ^ n then throw .overflow else pure (a + b) := by
  simp [add, BitVec.uaddOverflow]

@[simp] theorem sub_unsigned (a b : BitVec n) :
    sub false a b = if a.toNat < b.toNat then throw .overflow else pure (a - b) := by
  simp [sub, BitVec.usubOverflow]

@[simp] theorem mul_unsigned (a b : BitVec n) :
    mul false a b = if a.toNat * b.toNat ≥ 2 ^ n then throw .overflow else pure (a * b) := by
  simp [mul, BitVec.umulOverflow]

/-- Unsigned widening never fails. -/
@[simp] theorem intCast_unsigned_widen (a : BitVec n) (m : Nat) (h : n ≤ m) :
    intCast false false m a = pure (a.setWidth m) := by
  have ha := a.isLt
  have hp : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) h
  have hfit : (a.toNat : Int) ≤ 2 ^ m - 1 := by
    have : ((2 ^ m : Nat) : Int) = 2 ^ m := by norm_cast
    omega
  simp only [intCast, val, Bool.false_eq_true, ↓reduceIte]
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

end Zig
