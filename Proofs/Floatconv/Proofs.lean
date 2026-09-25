import Proofs.Floatconv.Gen

/-!
# Proofs about `examples/floatconv/floatconv.zig`

Int/float conversions and bit reinterpretation (`docs/floats.md` §Semantics: `@intFromFloat`,
`@floatFromInt`, `@floatCast`, `@bitCast`). Local helper lemmas are named to move into a
general `ZigLean/Float/Lemmas.lean` later.
-/

open Floatconv

namespace Zig

/-- A NaN's `classify` is `.nan` (unfolds the `isNaN` predicate back to the class it tests). -/
theorem Float.classify_eq_nan_of_isNaN {fmt : FloatFmt} (x : Float fmt) (h : x.isNaN) :
    x.classify = .nan := by
  unfold Float.isNaN at h
  cases hc : x.classify with
  | nan => rfl
  | inf s => simp [hc] at h
  | finite s m e => simp [hc] at h

/-- `@intFromFloat` of a NaN always throws `.unspecified`, whether or not the safety check is
active (`Float.toInt`'s `.nan` case ignores `safe`). -/
theorem Float.toInt_of_isNaN {fmt : FloatFmt} (s : Bool) (n : Nat) (safe : Bool) (x : Float fmt)
    (h : x.isNaN) : Float.toInt s n safe x = throw .unspecified := by
  unfold Float.toInt
  rw [Float.classify_eq_nan_of_isNaN x h]

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
