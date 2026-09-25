import Proofs.Floats.Gen

/-!
# Proofs about `examples/floats/floats.zig`

`isNan` is `x != x`, `clamp` is `lo`/`hi`-bounded, `celsius` is `null` below 0 K's Celsius
offset, `dot` is a slice dot-product, `lerp`/`hypot2` are plain arithmetic. Local helper
lemmas are named to move into a general `ZigLean/Float/Lemmas.lean` later.
-/

open Floats

namespace Zig

/-- `x != x` iff `x` is NaN: `Float.eq`'s `.nan` cases short-circuit before either operand's
value is inspected, and every other class compares equal to itself. -/
theorem Float.ne_self_eq_isNaN {fmt : FloatFmt} (x : Float fmt) : Float.ne x x = x.isNaN := by
  unfold Float.ne Float.eq Float.isNaN
  cases x.classify <;> simp

end Zig

/-- `isNan` is exactly `Float.isNaN` (`docs/floats.md` NaN semantics: `x != x`). -/
theorem isNan_spec (x : Zig.F64) : isNan x = pure (Zig.Float.isNaN x) := by
  unfold isNan
  simp [zig_unfold, Zig.Float.ne_self_eq_isNaN]
