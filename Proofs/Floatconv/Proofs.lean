import ZigLean.Float.RoundTrip
import Proofs.Floatconv.Gen

/-!
# Proofs about `examples/floatconv/floatconv.zig`

Int/float conversions and bit reinterpretation (`docs/floats.md` §Semantics: `@intFromFloat`,
`@floatFromInt`, `@floatCast`, `@bitCast`). Local helper lemmas are named to move into a
general `ZigLean/Float/Lemmas.lean` later.
-/

open Floatconv

namespace Zig

/-- `@intFromFloat` of a NaN always throws `.unspecified`, whether or not the safety check is
active (`Float.toInt`'s `.nan` case ignores `safe`). -/
theorem Float.toInt_of_isNaN {fmt : FloatFmt} (s : Bool) (n : Nat) (safe : Bool) (x : Float fmt)
    (h : x.isNaN) : Float.toInt s n safe x = throw .unspecified := by
  unfold Float.toInt
  rw [(Zig.isNaN_iff x).mp h]

end Zig

/-- `toByte` of a NaN throws `.unspecified` (`docs/floats.md`: `@intFromFloat` of NaN, the
safety check does not catch it). -/
theorem toByte_nan (x : Zig.F32) (h : x.isNaN) : toByte x = throw .unspecified := by
  unfold toByte
  simp [zig_unfold, Zig.Float.toInt_of_isNaN _ _ _ _ h]

/-- `@bitCast` of a NaN to an integer throws `.unspecified` (`docs/floats.md`: NaN has no
defined bit pattern to bit-cast). -/
theorem bits32_nan (x : Zig.F32) (h : x.isNaN) : bits32 x = throw .unspecified := by
  unfold bits32 Zig.Float.toBits?
  simp [zig_unfold, h]

/-- `@bitCast` of a non-NaN float to an integer is exactly its bits. -/
theorem bits32_ok (x : Zig.F32) (h : ¬ x.isNaN) : bits32 x = pure x.bits := by
  unfold bits32 Zig.Float.toBits?
  simp [zig_unfold, h]
  rfl

/-- `toByte` (`@intFromFloat` to `u8`, safety on) of a float whose exact value lies in `(-1, 256)`
succeeds, returning the truncation-toward-zero of that value. -/
theorem toByte_ok (x : Zig.F32) {q : Rat} (hx : x.toRat? = some q) (hlo : -1 < q) (hhi : q < 256) :
    toByte x = pure (BitVec.ofNat 8 (Zig.truncRat q).toNat) := by
  unfold toByte
  simp only [zig_unfold]
  rw [Zig.toInt_of_toRat hx]
  have h1 : ¬ Zig.truncRat q < 0 := by
    rw [Zig.truncRat_lt_zero_iff]
    exact Rat.not_le.mpr hlo
  have h2 : ¬ Zig.truncRat q > 255 := by
    rw [Zig.truncRat_gt_iff (by decide : (0:Int) ≤ 255)]
    have heq : ((255:Int) : Rat) + 1 = 256 := by grind
    rw [heq]
    exact Rat.not_le.mpr hhi
  have hnn : (0:Int) ≤ Zig.truncRat q := by omega
  have htoNat : ((Zig.truncRat q).toNat : Int) = Zig.truncRat q := Int.toNat_of_nonneg hnn
  have hbv : BitVec.ofInt 8 (Zig.truncRat q) = BitVec.ofNat 8 (Zig.truncRat q).toNat := by
    conv => lhs; rw [← htoNat]
    exact BitVec.ofInt_natCast 8 (Zig.truncRat q).toNat
  simp [zig_unfold, h1, h2, hbv]

/-- `toByte` (`@intFromFloat` to `u8`, safety on) of a finite float throws `.overflow` iff its
exact value lies outside `[-1, 256]`. -/
theorem toByte_overflow_of_finite (x : Zig.F32) {q : Rat} (hx : x.toRat? = some q) :
    toByte x = throw .overflow ↔ q ≤ -1 ∨ 256 ≤ q := by
  unfold toByte
  simp only [zig_unfold]
  rw [Zig.toInt_of_toRat hx]
  have h1 : Zig.truncRat q < 0 ↔ q ≤ -1 := Zig.truncRat_lt_zero_iff
  have h2 : Zig.truncRat q > 255 ↔ 256 ≤ q := by
    rw [Zig.truncRat_gt_iff (by decide : (0:Int) ≤ 255)]
    have heq : ((255:Int) : Rat) + 1 = 256 := by grind
    rw [heq]
  by_cases hcond : Zig.truncRat q < 0 ∨ Zig.truncRat q > 255
  · have hb : (decide (Zig.truncRat q < 0) || decide (Zig.truncRat q > 255)) = true := by
      rw [Bool.or_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq]
      exact hcond
    simp [hb, zig_unfold]
    exact hcond.imp h1.mp h2.mp
  · have hne := not_or.mp hcond
    have hnq : ¬ (q ≤ -1 ∨ 256 ≤ q) := not_or.mpr ⟨fun h => hne.1 (h1.mpr h), fun h => hne.2 (h2.mpr h)⟩
    simp [zig_unfold, hne.1, hne.2, hnq]
    intro h
    injection h with h'
    injection h'

/-- `toByte` (`@intFromFloat` to `u8`, safety on) of an infinite float throws `.overflow`
(`Float.toInt`'s `.inf` case ignores the exact magnitude and always panics when `safe`). -/
theorem toByte_overflow_of_inf (x : Zig.F32) (h : x.isInf) : toByte x = throw .overflow := by
  unfold toByte
  simp only [zig_unfold]
  unfold Zig.Float.isInf at h
  cases hc : x.classify with
  | inf s => unfold Zig.Float.toInt; rw [hc]; simp [zig_unfold]
  | nan => rw [hc] at h; simp at h
  | finite _ _ _ => rw [hc] at h; simp at h
