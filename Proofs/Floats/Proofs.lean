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

/-- A NaN's `classify` is `.nan` (unfolds the `isNaN` predicate back to the class it tests). -/
theorem Float.classify_eq_nan_of_isNaN {fmt : FloatFmt} (x : Float fmt) (h : x.isNaN) :
    x.classify = .nan := by
  unfold Float.isNaN at h
  cases hc : x.classify with
  | nan => rfl
  | inf s => simp [hc] at h
  | finite s m e => simp [hc] at h

/-- The canonical quiet NaN classifies as NaN, in every format. -/
theorem Float.isNaN_nan {fmt : FloatFmt} : (Float.nan : Float fmt).isNaN = true := by
  cases fmt <;> decide

/-- `a - b` is NaN whenever `a` is (`Float.sub`/`Float.add`'s `.nan` case short-circuits before
`b` is inspected). -/
theorem Float.isNaN_sub_left {fmt : FloatFmt} (a b : Float fmt) (h : a.isNaN) :
    (Float.sub a b).isNaN := by
  have ha := Float.classify_eq_nan_of_isNaN a h
  unfold Float.sub Float.add
  rw [ha]
  exact Float.isNaN_nan

/-- `pure (some x)` is never `pure none` in the `Zig.Result` monad (the `Option` constructors
stay distinct once wrapped in `Except.ok`). -/
theorem pure_some_ne_none {α : Type} (x : α) :
    (pure (some x) : Zig.Result (Option α)) ≠ pure none := by
  show some (Except.ok (some x)) ≠ some (Except.ok none)
  simp

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

/-- `celsius`'s monadic scaffolding reduces to a plain `if` on `k < 0`, regardless of which
branch is taken (the surrounding `StateT`/`ExceptT` plumbing is the same shape either way). -/
theorem celsius_body (k : Zig.F32) : celsius k =
    if Zig.Float.lt k (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) then pure none
    else pure (some (Zig.Float.sub k (Zig.Float.ofBits (1133024051 : BitVec 32) : Zig.F32))) := by
  unfold celsius
  cases hlt : Zig.Float.lt k (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) <;> rfl

/-- `celsius k = none` iff `k < 0` (the Kelvin value is below absolute zero's Celsius
representation is never reached: the check is on `k` itself, before the offset). Holds for
every `k`, NaN included — `Float.lt`'s `.nan` case is `false`, matching `celsius`'s `else`
branch, so the unused hypothesis only documents the caller's expected precondition. -/
theorem celsius_null_iff (k : Zig.F32) (_h : ¬ k.isNaN) :
    celsius k = pure none ↔ Zig.Float.lt k (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) := by
  rw [celsius_body]
  cases hlt : Zig.Float.lt k (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32)
  · simp [Zig.pure_some_ne_none]
  · simp

/-- `celsius` of a NaN never returns `none`: it takes the `else` branch (`k < 0` is `false` for
NaN) and subtracts, propagating the NaN. -/
theorem celsius_nan (k : Zig.F32) (h : k.isNaN) :
    ∃ r, celsius k = pure (some r) ∧ r.isNaN := by
  have hlt : Zig.Float.lt k (Zig.Float.ofBits (0 : BitVec 32) : Zig.F32) = false := by
    have hc := Zig.Float.classify_eq_nan_of_isNaN k h
    unfold Zig.Float.lt
    rw [hc]
  refine ⟨Zig.Float.sub k (Zig.Float.ofBits (1133024051 : BitVec 32) : Zig.F32), ?_, ?_⟩
  · rw [celsius_body, hlt]; rfl
  · exact Zig.Float.isNaN_sub_left k _ h

