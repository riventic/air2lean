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

/-- A non-NaN value equals itself (`Float.eq`'s `.nan` case is the only one that isn't
reflexive). -/
theorem Float.eq_refl {fmt : FloatFmt} (a : Float fmt) (ha : ¬a.isNaN) : Float.eq a a = true := by
  unfold Float.eq
  unfold Float.isNaN at ha
  cases hca : a.classify with
  | nan => simp [hca] at ha
  | inf s => simp
  | finite s m e => simp

/-- A non-NaN value is `≤` itself (`Float.le`'s `eq` disjunct, via `Float.eq_refl`). -/
theorem Float.le_refl {fmt : FloatFmt} (a : Float fmt) (ha : ¬a.isNaN) : Float.le a a = true := by
  unfold Float.le
  rw [Float.eq_refl a ha]
  simp

/-- For non-NaN operands, `¬(a < b)` gives `b ≤ a` (the missing half of `Float.lt`/`Float.le`'s
totality: NaN is the only case where neither direction holds). -/
theorem Float.le_of_not_lt {fmt : FloatFmt} {a b : Float fmt} (ha : ¬a.isNaN) (hb : ¬b.isNaN)
    (h : Float.lt a b = false) : Float.le b a = true := by
  unfold Float.isNaN at ha hb
  unfold Float.lt at h
  unfold Float.le Float.lt Float.eq
  cases hca : a.classify with
  | nan => simp [hca] at ha
  | inf sa =>
    cases hcb : b.classify with
    | nan => simp [hcb] at hb
    | inf sb =>
      rw [hca, hcb] at h
      cases sa <;> cases sb <;> simp_all
    | finite sb mb eb =>
      rw [hca, hcb] at h
      simp_all
  | finite sa ma ea =>
    cases hcb : b.classify with
    | nan => simp [hcb] at hb
    | inf sb =>
      rw [hca, hcb] at h
      simp_all
    | finite sb mb eb =>
      rw [hca, hcb] at h
      have h' : ¬ (finiteToRat sa ma ea < finiteToRat sb mb eb) := of_decide_eq_false h
      have h'' : finiteToRat sb mb eb ≤ finiteToRat sa ma ea := Rat.not_lt.mp h'
      cases Rat.le_iff_lt_or_eq.mp h'' with
      | inl hlt => simp [hlt]
      | inr heq => simp [heq]

/-- For non-NaN operands, `a ≤ b` gives `¬(b < a)` (the converse of `Float.le_of_not_lt`: `≤`
and the reverse strict order are mutually exclusive). -/
theorem Float.lt_eq_false_of_le {fmt : FloatFmt} {a b : Float fmt} (ha : ¬a.isNaN) (hb : ¬b.isNaN)
    (h : Float.le a b = true) : Float.lt b a = false := by
  unfold Float.isNaN at ha hb
  unfold Float.le at h
  unfold Float.lt at *
  cases hca : a.classify with
  | nan => simp [hca] at ha
  | inf sa =>
    cases hcb : b.classify with
    | nan => simp [hcb] at hb
    | inf sb =>
      rw [hca, hcb] at h
      unfold Float.eq at h
      rw [hca, hcb] at h
      cases sa <;> cases sb <;> simp_all
    | finite sb mb eb =>
      rw [hca, hcb] at h
      unfold Float.eq at h
      rw [hca, hcb] at h
      simp_all
  | finite sa ma ea =>
    cases hcb : b.classify with
    | nan => simp [hcb] at hb
    | inf sb =>
      rw [hca, hcb] at h
      unfold Float.eq at h
      rw [hca, hcb] at h
      simp_all
    | finite sb mb eb =>
      rw [hca, hcb] at h
      unfold Float.eq at h
      rw [hca, hcb] at h
      have hor : finiteToRat sa ma ea < finiteToRat sb mb eb ∨
          finiteToRat sa ma ea = finiteToRat sb mb eb := by
        match Bool.or_eq_true_iff.mp h with
        | .inl h1 => exact Or.inl (of_decide_eq_true h1)
        | .inr h1 => exact Or.inr (eq_of_beq h1)
      have hle2 : finiteToRat sa ma ea ≤ finiteToRat sb mb eb :=
        Rat.le_iff_lt_or_eq.mpr hor
      exact decide_eq_false (Rat.not_lt.mpr hle2)

end Zig

/-- `isNan` is exactly `Float.isNaN` (`docs/floats.md` NaN semantics: `x != x`). -/
theorem isNan_spec (x : Zig.F64) : isNan x = pure (Zig.Float.isNaN x) := by
  unfold isNan
  simp [zig_unfold, Zig.eq_self]

/-- `clamp`'s monadic scaffolding reduces to a plain nested `if` on `x < lo` / `x > hi`. -/
theorem clamp_body (x lo hi : Zig.F32) : clamp x lo hi =
    pure (if Zig.Float.lt x lo then lo else if Zig.Float.gt x hi then hi else x) := by
  unfold clamp
  cases h1 : Zig.Float.lt x lo <;> cases h2 : Zig.Float.gt x hi <;> rfl

/-- `clamp x lo hi` always lands in `[lo, hi]`, for non-NaN operands with `lo ≤ hi`. -/
theorem clamp_spec (x lo hi : Zig.F32) (hxn : ¬x.isNaN) (hlon : ¬lo.isNaN) (hhin : ¬hi.isNaN)
    (hle : Zig.Float.le lo hi) :
    ∃ r, clamp x lo hi = pure r ∧ Zig.Float.le lo r ∧ Zig.Float.le r hi := by
  rw [clamp_body]
  cases h1 : Zig.Float.lt x lo with
  | true => exact ⟨lo, rfl, Zig.Float.le_refl lo hlon, hle⟩
  | false =>
    cases h2 : Zig.Float.gt x hi with
    | true => exact ⟨hi, rfl, hle, Zig.Float.le_refl hi hhin⟩
    | false =>
      refine ⟨x, rfl, Zig.Float.le_of_not_lt hxn hlon h1, ?_⟩
      exact Zig.Float.le_of_not_lt hhin hxn h2

/-- `clamp x lo hi = x` when `x` is already in `[lo, hi]` (non-NaN operands). -/
theorem clamp_id (x lo hi : Zig.F32) (hxn : ¬x.isNaN) (hlon : ¬lo.isNaN) (hhin : ¬hi.isNaN)
    (hlex : Zig.Float.le lo x) (hxhi : Zig.Float.le x hi) : clamp x lo hi = pure x := by
  rw [clamp_body]
  have h1 : Zig.Float.lt x lo = false := Zig.Float.lt_eq_false_of_le hlon hxn hlex
  have h2 : Zig.Float.gt x hi = false := Zig.Float.lt_eq_false_of_le hxn hhin hxhi
  rw [h1, h2]
  rfl

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

/-- `dot` of two slices with different lengths panics (the length check before the loop). -/
theorem dot_len_mismatch (xs ys : Array Zig.F64) (hxs : xs.size < 2 ^ 64) (hys : ys.size < 2 ^ 64)
    (h : xs.size ≠ ys.size) : dot xs ys = throw .panic := by
  unfold dot
  have hne : Zig.len xs ≠ Zig.len ys := by
    unfold Zig.len
    intro hc
    apply h
    have := congrArg BitVec.toNat hc
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxs, Nat.mod_eq_of_lt hys] at this
  simp [zig_unfold, hne]

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

