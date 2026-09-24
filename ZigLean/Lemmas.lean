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

end Zig
