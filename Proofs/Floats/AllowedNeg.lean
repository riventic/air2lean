import ZigLean.Float.Allowed

/-!
# Allowed float results: negative tests (F04)

`ZigLean/Float/Allowed.lean` states the results a target may give where the model picks one.
A proof stated with `Float.Allowed`/`Float.MinAllowed` covers every target only if the relation
really admits the other results; and the variation must never turn an illegal operand into a
value. These theorems pin both on concrete f32 values, by kernel evaluation and without the
library's own lemmas about the relation:

* `nan_varies`: a NaN of another sign and payload is an allowed result of a NaN, and it is not
  the model's NaN.
* `min_zero_varies`: `@min(+0, −0)` (group D) may give either zero.
* `toInt_allowed_nan`: `@intFromFloat` of every allowed result of a NaN throws `.illegal`,
  with or without the safety check.

`scripts/mutate.sh` mutations (ag) and (ah) collapse the relation to the model's result; the
build of this module must fail under each (assurance/mutation-kills.json).
-/

namespace Zig.AllowedNeg

/-- The f32 quiet NaN `0x7fc00000`. -/
def qnan : F32 := Float.ofBits 0x7fc00000#32

/-- The f32 NaN `0xffc00001`: another sign and another payload. -/
def otherNan : F32 := Float.ofBits 0xffc00001#32

theorem qnan_classify : qnan.classify = .nan := by decide +kernel

/-- Variation is real: the target may return another NaN than the model's. -/
theorem nan_varies : Float.Allowed qnan otherNan ∧ otherNan ≠ qnan := by
  unfold Float.Allowed
  decide +kernel

/-- Group D: `@min(+0, −0)` may return either zero. -/
theorem min_zero_varies :
    Float.MinAllowed (Float.zero false : F32) (Float.zero true) (Float.zero false) ∧
      Float.MinAllowed (Float.zero false : F32) (Float.zero true) (Float.zero true) := by
  unfold Float.MinAllowed Float.Allowed
  decide +kernel

/-- Errors stay errors: a NaN operand of `@intFromFloat` throws `.illegal` whichever NaN the
target produced, checked or unchecked. -/
theorem toInt_allowed_nan {r : F32} (h : Float.Allowed qnan r) (s : Bool) (n : Nat) (safe : Bool) :
    Float.toInt s n safe r = throw .illegal := by
  rw [Float.toInt_allowed s n safe h]
  unfold Float.toInt
  rw [qnan_classify]

end Zig.AllowedNeg
