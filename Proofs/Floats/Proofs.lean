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

/-- `dot` of two empty slices is `+0` (the model's zero result, no addends). -/
theorem dot_nil : dot (#[] : Array Zig.F64) (#[] : Array Zig.F64) =
    pure (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) := by
  have hbody : (dot.loop18 (#[] : Array Zig.F64) #[] (0 : BitVec 64)).run
      ({ s := Zig.Float.ofBits (0 : BitVec 64), local6 := 0 } : dotLocals) =
      pure (dotExit.br17, ({ s := Zig.Float.ofBits (0 : BitVec 64), local6 := 0 } : dotLocals)) := by
    unfold dot.loop18
    simp [zig_unfold, Zig.lt]
  have hloop := Zig.loop_run (dot.loop18 (#[] : Array Zig.F64) #[] (0 : BitVec 64)) dot.again18
    ({ s := Zig.Float.ofBits (0 : BitVec 64), local6 := 0 } : dotLocals)
  rw [hbody] at hloop
  simp [zig_unfold, dot.again18] at hloop
  unfold dot
  simp [zig_unfold, Zig.len, hloop]
