import ZigLean.Sep.Full.AutoRules

/-!
# Rules for the arithmetic and copies of growing slices

Code that grows a buffer of items (`std.ArrayList`'s `ensureTotalCapacityPrecise` and its
`growCapacity`) multiplies an item count by the item size with a checked `*`, grows a capacity
with a saturating `+|`, forms the pointer to item `0` of a buffer that may have no bytes, and
copies no items with `@memcpy` when the old buffer is empty. Four rules for `fsym`, for every
width, item size and pointer:

* `mul_step`: a checked unsigned `*` that does not overflow returns the product.
* `addSat_false`: the value of an unsigned `+|` (an `fsym_arith` equation).
* `ptrProject_elem_zero`: the pointer to item `0` is the pointer itself; formed for any pointer
  (MM-3), so it needs no ownership.
* `memcpy_zero`: `@memcpy` of no items does nothing, whatever the pointers are.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig.Full

open FAssn

/-- A checked unsigned `*` that does not overflow. -/
@[fsym] theorem mul_step {w : Nat} {P : FAssn} {a b : BitVec w} (h : a.toNat * b.toNat < 2 ^ w) :
    FTotalTriple P (StateT.lift (Zig.mul false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat * b.toNat⟫ ⋆ P) := by
  have e : Zig.mul false a b = pure (a * b) := by
    simp only [Zig.mul, BitVec.umulOverflow, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hc; simp at hc; omega
    · rfl
  rw [e]; exact Auto.read_val (BitVec.toNat_mul_of_lt h)

/-- Unsigned `+|`, as of the values. -/
@[fsym_arith] theorem addSat_false {w : Nat} (a b : BitVec w) :
    (Zig.addSat false a b).toNat = Min.min (a.toNat + b.toNat) (2 ^ w - 1) := by
  unfold Zig.addSat Zig.clamp Zig.val
  simp only [Bool.false_eq_true, ↓reduceIte, Zig.intLo_unsigned, Zig.intHi_unsigned]
  rw [BitVec.toNat_ofInt]
  have ha := a.isLt; have hb := b.isLt
  have h0 : (0 : Nat) < 2 ^ w := Nat.two_pow_pos w
  have e : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by push_cast; rfl
  rw [e]
  generalize 2 ^ w = N at *
  have hm : Max.max 0 (Min.min ((N : Int) - 1) (↑a.toNat + ↑b.toNat)) =
      ((Min.min (a.toNat + b.toNat) (N - 1) : Nat) : Int) := by omega
  rw [hm, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

/-- `@memcpy` of no items: nothing. -/
@[fsym] theorem memcpy_zero {P : FAssn} {sz da sa : Nat} {d s : Ptr} {n m : BitVec 64}
    (hn : n.toNat = 0) (hm : m.toNat = 0) : FTotalTriple P (Zig.memcpy sz da sa d s n m) (fun _ => P) := by
  have e : Zig.memcpy sz da sa d s n m = pure () := by
    have : n = m := BitVec.eq_of_toNat_eq (by omega)
    subst this
    simp [Zig.memcpy, Zig.memmove, Ptr.overlaps, hn]
  rw [e]; exact FTotalTriple.ret (Q := fun _ => P) ()

/-- The pointer to item `0`: the pointer itself (formed for any pointer, MM-3). -/
@[fsym] theorem ptrProject_elem_zero {P : FAssn} {p : Ptr} {s : Nat} {i : BitVec 64} (hi : i.toNat = 0) :
    FTotalTriple P (ptrProject p (·.elem s i)) (fun q => ⟪q = p⟫ ⋆ P) := by
  have e : (fun x : Ptr => x.elem s i) = fun x => x := by
    funext x; simp [Ptr.elem, hi, Ptr.add]
  rw [e]
  exact FTotalTriple.of_read fun m _ _ _ _ _ => ptrProject_id p m

end Zig.Full
