import ZigLean.VecMem
import ZigLean.ReprCast

/-!
# Zig ≤0.16 `@bitCast` with a vector side (proof-only, L09)

Up to Zig 0.16.0 a `@bitCast` reinterprets memory (`Zig.reprCast`, `docs/aggregate-casts.md`).
A vector's memory image is the integer of its lane bits (`Vec.packedEnc`: lane `i` at bits
`[i * w, (i + 1) * w)`), so a cast between `@Vector(n, uW)` and the integer of its `n * W` bits
is that integer, for every lane width, whole-byte or not (the LLVM backend's `bitcast`, which
`Check.lean` admits through `modelLayout`). `[n]T` ↔ `@Vector(n, T)` is translated lane-wise
(`Air2Lean/Check.lean`'s `vectorLaneCast?`), not through these lemmas.

* `reprCast_vec_int`: vector → integer is `Vec.packBits`.
* `reprCast_int_vec`: integer → vector splits the integer into lanes (`laneOf`).
* `reprCast_int_vec_int`: the round trip integer → vector → integer is the identity.
-/

namespace Zig

private theorem extract_padTo_padTo (a b : Nat) (xs : Array Byte) :
    (padTo a (padTo b xs)).extract 0 xs.size = xs := by
  simp [padTo, Array.extract_append]

theorem reprCast_vec_int {n w : Nat} (v : Vec (BitVec w) n) :
    reprCast (BitVec (n * w)) v = pure (v.packBits w id) := by
  unfold reprCast
  apply intOfBytes_of_extract
  have hs : (intBytes (v.packBits w id)).size = (n * w + 7) / 8 := by simp [intBytes]
  rw [← hs]
  exact extract_padTo_padTo _ _ _

theorem reprCast_int_vec {n w : Nat} (x : BitVec (n * w)) :
    reprCast (Vec (BitVec w) n) x = pure ⟨Vector.ofFn fun i => laneOf w x.toNat i⟩ := by
  unfold reprCast
  have hs : (intBytes x).size = (n * w + 7) / 8 := by simp [intBytes]
  have hx : intOfBytes (n * w) (padTo (packedVecLayout n w) (padTo (intSize (n * w)) (intBytes x))) =
      pure x := by
    apply intOfBytes_of_extract
    rw [← hs]
    exact extract_padTo_padTo _ _ _
  simp only [Enc.decode, Enc.size, Enc.encode, hx]
  rfl

/-- Splitting `x < 2 ^ (n * w)` into `n` lanes and packing them again gives `x`. -/
theorem packLanes_range_laneOf (w : Nat) :
    ∀ (n x : Nat), x < 2 ^ (n * w) → packLanes ((List.range n).map (laneOf w x)) = x
  | 0, x, h => by simp at h; simp [packLanes, h]
  | n + 1, x, h => by
    have hlane : ∀ i, laneOf w x (i + 1) = laneOf w (x >>> w) i := by
      intro i
      simp only [laneOf]
      rw [Nat.succ_mul, Nat.add_comm (i * w) w, Nat.shiftRight_add]
    have hrest : x >>> w < 2 ^ (n * w) := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_comm, ← Nat.succ_mul]; exact h
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [packLanes, Function.comp_def, hlane]
    rw [packLanes_range_laneOf w n (x >>> w) hrest]
    simp only [laneOf, Nat.zero_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.pow_zero, Nat.div_one]
    exact Nat.mod_add_div x (2 ^ w)

/-- `@bitCast(@as(@Vector(n, uW), @bitCast(x)))` is `x`. -/
theorem reprCast_int_vec_int {n w : Nat} (x : BitVec (n * w)) :
    (reprCast (Vec (BitVec w) n) x >>= reprCast (BitVec (n * w))) = pure x := by
  rw [reprCast_int_vec, pure_bind, reprCast_vec_int]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [Vec.packBits_toNat]
  have hl : (Vector.ofFn fun i : Fin n => laneOf w x.toNat i).toList.map id =
      (List.range n).map (laneOf w x.toNat) := by
    apply List.ext_getElem <;> simp
  rw [hl]
  exact packLanes_range_laneOf w n x.toNat x.isLt

end Zig
