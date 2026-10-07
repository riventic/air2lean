import Proofs.Floatops.Gen
import ZigLean.Float.RoundTrip

/-!
# Proofs about `examples/floatops/floatops.zig`

`floatops` is a test bench: `opN` dispatches on `sel` to one float op, and the diff test checks
each op against the compiled Zig bit for bit. The proofs here state what does not depend on the
Zig version: the division selectors (3, 5, 6) call a different model function per version
(`docs/floats.md` §Per-version differences), and CI builds these proofs against each version's
translation.

- `opN_spec`: every `sel` picks its op (`opSpec`). `/`, `@divTrunc` and `@divFloor` are
  `Float.div` on every version for `f16`..`f80`; `op128_spec` leaves out `sel` 3, 5, 6, 9
  (`f128` division and `@sqrt` differ by version). Multiplication and remainder use the
  compiler-rt helpers selected by this example. `op80_spec` excludes a pseudo-denormal
  numerator because f80 floor/ceil changed in 0.16.0. `opN_other`: a `sel` of 26 or more returns
  `a` unchanged.
- `divExact64_spec`: the truncated quotient, or a panic when it is not a whole number.
- `cmp64_spec`: the bitmask is the 6 comparisons; `cmp64_nan`: with a NaN operand only `!=` is
  true (IEEE 754: NaN is unordered), so the mask is `8`.
-/

open Floatops

/-- The bitmask of `cmp64`: bit 0 `<`, bit 1 `<=`, bit 2 `==`, bit 3 `!=`, bit 4 `>=`, bit 5 `>`. -/
def cmpMask {fmt : Zig.FloatFmt} (a b : Zig.Float fmt) : BitVec 8 :=
  (if Zig.Float.lt a b then 1 else 0) ||| (if Zig.Float.le a b then 2 else 0) |||
  (if Zig.Float.eq a b then 4 else 0) ||| (if Zig.Float.ne a b then 8 else 0) |||
  (if Zig.Float.ge a b then 16 else 0) ||| (if Zig.Float.gt a b then 32 else 0)

theorem cmp64_spec (a b : Zig.F64) : cmp64 a b = pure (cmpMask a b) := by
  unfold cmp64 cmpMask
  generalize Zig.Float.lt a b = x1
  generalize Zig.Float.le a b = x2
  generalize Zig.Float.eq a b = x3
  generalize Zig.Float.ne a b = x4
  generalize Zig.Float.ge a b = x5
  generalize Zig.Float.gt a b = x6
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> cases x6 <;> rfl

theorem classify_of_isNaN {fmt : Zig.FloatFmt} {x : Zig.Float fmt} (h : x.isNaN = true) :
    x.classify = .nan := by
  unfold Zig.Float.isNaN at h; split at h <;> simp_all

/-- `<` with a NaN operand is false. -/
theorem lt_nan {fmt : Zig.FloatFmt} {a b : Zig.Float fmt} (h : a.isNaN ∨ b.isNaN) :
    Zig.Float.lt a b = false := by
  unfold Zig.Float.lt
  rcases h with h | h <;> rw [classify_of_isNaN h] <;>
    rcases a.classify with _ | _ | _ <;> rcases b.classify with _ | _ | _ <;> rfl

/-- `==` with a NaN operand is false, also NaN == NaN. -/
theorem eq_nan {fmt : Zig.FloatFmt} {a b : Zig.Float fmt} (h : a.isNaN ∨ b.isNaN) :
    Zig.Float.eq a b = false := by
  unfold Zig.Float.eq
  rcases h with h | h <;> rw [classify_of_isNaN h] <;>
    rcases a.classify with _ | _ | _ <;> rcases b.classify with _ | _ | _ <;> rfl

theorem cmpMask_nan {fmt : Zig.FloatFmt} (a b : Zig.Float fmt) (h : a.isNaN ∨ b.isNaN) :
    cmpMask a b = 8 := by
  have h' : b.isNaN ∨ a.isNaN := h.symm
  simp only [cmpMask, Zig.Float.le, Zig.Float.ne, Zig.Float.ge, Zig.Float.gt, lt_nan h,
    lt_nan h', eq_nan h, eq_nan h']
  rfl

theorem cmp64_nan (a b : Zig.F64) (h : a.isNaN ∨ b.isNaN) : cmp64 a b = pure 8 := by
  rw [cmp64_spec, cmpMask_nan a b h]

/-- A `sel` of 26 or more is not one of the 26 op selectors. -/
theorem sel_ne {sel : BitVec 8} (h : 26 ≤ sel.toNat) (k : BitVec 8) (hk : k.toNat < 26) :
    (sel == k) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro he; subst he; omega

theorem op16_other (sel : BitVec 8) (h : 26 ≤ sel.toNat) (a b c : Zig.Float .f16) :
    op16 sel a b c = pure a := by
  unfold op16
  simp only [sel_ne h 0 (by decide), sel_ne h 1 (by decide), sel_ne h 2 (by decide),
    sel_ne h 3 (by decide), sel_ne h 4 (by decide), sel_ne h 5 (by decide),
    sel_ne h 6 (by decide), sel_ne h 7 (by decide), sel_ne h 8 (by decide),
    sel_ne h 9 (by decide), sel_ne h 10 (by decide), sel_ne h 11 (by decide),
    sel_ne h 12 (by decide), sel_ne h 13 (by decide), sel_ne h 14 (by decide),
    sel_ne h 15 (by decide), sel_ne h 16 (by decide), sel_ne h 17 (by decide),
    sel_ne h 18 (by decide), sel_ne h 19 (by decide), sel_ne h 20 (by decide),
    sel_ne h 21 (by decide), sel_ne h 22 (by decide), sel_ne h 23 (by decide),
    sel_ne h 24 (by decide), sel_ne h 25 (by decide)]
  rfl

theorem op32_other (sel : BitVec 8) (h : 26 ≤ sel.toNat) (a b c : Zig.F32) :
    op32 sel a b c = pure a := by
  unfold op32
  simp only [sel_ne h 0 (by decide), sel_ne h 1 (by decide), sel_ne h 2 (by decide),
    sel_ne h 3 (by decide), sel_ne h 4 (by decide), sel_ne h 5 (by decide),
    sel_ne h 6 (by decide), sel_ne h 7 (by decide), sel_ne h 8 (by decide),
    sel_ne h 9 (by decide), sel_ne h 10 (by decide), sel_ne h 11 (by decide),
    sel_ne h 12 (by decide), sel_ne h 13 (by decide), sel_ne h 14 (by decide),
    sel_ne h 15 (by decide), sel_ne h 16 (by decide), sel_ne h 17 (by decide),
    sel_ne h 18 (by decide), sel_ne h 19 (by decide), sel_ne h 20 (by decide),
    sel_ne h 21 (by decide), sel_ne h 22 (by decide), sel_ne h 23 (by decide),
    sel_ne h 24 (by decide), sel_ne h 25 (by decide)]
  rfl

theorem op64_other (sel : BitVec 8) (h : 26 ≤ sel.toNat) (a b c : Zig.F64) :
    op64 sel a b c = pure a := by
  unfold op64
  simp only [sel_ne h 0 (by decide), sel_ne h 1 (by decide), sel_ne h 2 (by decide),
    sel_ne h 3 (by decide), sel_ne h 4 (by decide), sel_ne h 5 (by decide),
    sel_ne h 6 (by decide), sel_ne h 7 (by decide), sel_ne h 8 (by decide),
    sel_ne h 9 (by decide), sel_ne h 10 (by decide), sel_ne h 11 (by decide),
    sel_ne h 12 (by decide), sel_ne h 13 (by decide), sel_ne h 14 (by decide),
    sel_ne h 15 (by decide), sel_ne h 16 (by decide), sel_ne h 17 (by decide),
    sel_ne h 18 (by decide), sel_ne h 19 (by decide), sel_ne h 20 (by decide),
    sel_ne h 21 (by decide), sel_ne h 22 (by decide), sel_ne h 23 (by decide),
    sel_ne h 24 (by decide), sel_ne h 25 (by decide)]
  rfl

theorem op80_other (sel : BitVec 8) (h : 26 ≤ sel.toNat) (a b c : Zig.Float .f80) :
    op80 sel a b c = pure a := by
  unfold op80
  simp only [sel_ne h 0 (by decide), sel_ne h 1 (by decide), sel_ne h 2 (by decide),
    sel_ne h 3 (by decide), sel_ne h 4 (by decide), sel_ne h 5 (by decide),
    sel_ne h 6 (by decide), sel_ne h 7 (by decide), sel_ne h 8 (by decide),
    sel_ne h 9 (by decide), sel_ne h 10 (by decide), sel_ne h 11 (by decide),
    sel_ne h 12 (by decide), sel_ne h 13 (by decide), sel_ne h 14 (by decide),
    sel_ne h 15 (by decide), sel_ne h 16 (by decide), sel_ne h 17 (by decide),
    sel_ne h 18 (by decide), sel_ne h 19 (by decide), sel_ne h 20 (by decide),
    sel_ne h 21 (by decide), sel_ne h 22 (by decide), sel_ne h 23 (by decide),
    sel_ne h 24 (by decide), sel_ne h 25 (by decide)]
  rfl

theorem op128_other (sel : BitVec 8) (h : 26 ≤ sel.toNat) (a b c : Zig.Float .f128) :
    op128 sel a b c = pure a := by
  unfold op128
  simp only [sel_ne h 0 (by decide), sel_ne h 1 (by decide), sel_ne h 2 (by decide),
    sel_ne h 3 (by decide), sel_ne h 4 (by decide), sel_ne h 5 (by decide),
    sel_ne h 6 (by decide), sel_ne h 7 (by decide), sel_ne h 8 (by decide),
    sel_ne h 9 (by decide), sel_ne h 10 (by decide), sel_ne h 11 (by decide),
    sel_ne h 12 (by decide), sel_ne h 13 (by decide), sel_ne h 14 (by decide),
    sel_ne h 15 (by decide), sel_ne h 16 (by decide), sel_ne h 17 (by decide),
    sel_ne h 18 (by decide), sel_ne h 19 (by decide), sel_ne h 20 (by decide),
    sel_ne h 21 (by decide), sel_ne h 22 (by decide), sel_ne h 23 (by decide),
    sel_ne h 24 (by decide), sel_ne h 25 (by decide)]
  rfl

/-! ### Every selector -/

/-- The op that `sel` picks, in the model (`docs/floats.md` §Semantics). `/`, `@divTrunc` and
`@divFloor` are `Float.div` then `trunc`/`floor`: on a format other than `f128` that is the
model of every Zig version. -/
def opSpec {fmt : Zig.FloatFmt} (sel : BitVec 8) (a b c : Zig.Float fmt) : Zig.Result (Zig.Float fmt) :=
  match sel.toNat with
  | 0 => pure (Zig.Float.add a b)
  | 1 => pure (Zig.Float.sub a b)
  | 2 => pure (Zig.Float.mulRt a b)
  | 3 => pure (Zig.Float.div a b)
  | 4 => Zig.Float.fmaRtChk a b c
  | 5 => pure (Zig.Float.trunc (Zig.Float.div a b))
  | 6 => pure (Zig.Float.floor (Zig.Float.div a b))
  | 7 => Zig.Float.remRtChk a b
  | 8 => Zig.Float.modRtChk a b
  | 9 => pure (Zig.Float.sqrt a)
  | 10 => Zig.Float.floorChk a
  | 11 => Zig.Float.ceilChk a
  | 12 => Zig.Float.truncChk a
  | 13 => Zig.Float.roundChk a
  | 14 => pure (Zig.Float.abs a)
  | 15 => pure (Zig.Float.neg a)
  | 16 => Zig.Float.minChk a b
  | 17 => Zig.Float.maxChk a b
  | 18 => pure (Zig.Float.libm .sin a)
  | 19 => pure (Zig.Float.libm .cos a)
  | 20 => pure (Zig.Float.libm .tan a)
  | 21 => pure (Zig.Float.libm .exp a)
  | 22 => pure (Zig.Float.libm .exp2 a)
  | 23 => pure (Zig.Float.libm .log a)
  | 24 => pure (Zig.Float.libm .log2 a)
  | 25 => pure (Zig.Float.libm .log10 a)
  | _ => pure a

theorem opSpec_other {fmt : Zig.FloatFmt} {sel : BitVec 8} (h : 26 ≤ sel.toNat)
    (a b c : Zig.Float fmt) : opSpec sel a b c = pure a := by
  unfold opSpec
  split <;> first | omega | rfl

/-- A `sel` below 26 is `BitVec.ofNat 8 n` for an `n` below 26. -/
theorem sel_lt {sel : BitVec 8} (h : ¬26 ≤ sel.toNat) :
    ∃ n, n < 26 ∧ sel = BitVec.ofNat 8 n :=
  ⟨sel.toNat, by omega, by simp⟩

theorem op16_spec (sel : BitVec 8) (a b c : Zig.Float .f16) : op16 sel a b c = opSpec sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op16_other sel h, opSpec_other h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ =>
      show _ = Zig.Float.fmaRtChk a b c
      unfold op16; generalize Zig.Float.fmaRtChk a b c = x; rcases x with _ | _ | _ <;> rfl
    | 7, _ =>
      show _ = Zig.Float.remRtChk a b
      unfold op16; generalize Zig.Float.remRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 8, _ =>
      show _ = Zig.Float.modRtChk a b
      unfold op16; generalize Zig.Float.modRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 10, _ =>
      show _ = Zig.Float.floorChk a
      unfold op16; generalize Zig.Float.floorChk a = x; rcases x with _ | _ | _ <;> rfl
    | 11, _ =>
      show _ = Zig.Float.ceilChk a
      unfold op16; generalize Zig.Float.ceilChk a = x; rcases x with _ | _ | _ <;> rfl
    | 12, _ =>
      show _ = Zig.Float.truncChk a
      unfold op16; generalize Zig.Float.truncChk a = x; rcases x with _ | _ | _ <;> rfl
    | 13, _ =>
      show _ = Zig.Float.roundChk a
      unfold op16; generalize Zig.Float.roundChk a = x; rcases x with _ | _ | _ <;> rfl
    | 16, _ =>
      show _ = Zig.Float.minChk a b
      unfold op16; generalize Zig.Float.minChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 17, _ =>
      show _ = Zig.Float.maxChk a b
      unfold op16; generalize Zig.Float.maxChk a b = x; rcases x with _ | _ | _ <;> rfl
    | n + 26, h => omega

theorem op32_spec (sel : BitVec 8) (a b c : Zig.Float .f32) : op32 sel a b c = opSpec sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op32_other sel h, opSpec_other h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ =>
      show _ = Zig.Float.fmaRtChk a b c
      unfold op32; generalize Zig.Float.fmaRtChk a b c = x; rcases x with _ | _ | _ <;> rfl
    | 7, _ =>
      show _ = Zig.Float.remRtChk a b
      unfold op32; generalize Zig.Float.remRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 8, _ =>
      show _ = Zig.Float.modRtChk a b
      unfold op32; generalize Zig.Float.modRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 10, _ =>
      show _ = Zig.Float.floorChk a
      unfold op32; generalize Zig.Float.floorChk a = x; rcases x with _ | _ | _ <;> rfl
    | 11, _ =>
      show _ = Zig.Float.ceilChk a
      unfold op32; generalize Zig.Float.ceilChk a = x; rcases x with _ | _ | _ <;> rfl
    | 12, _ =>
      show _ = Zig.Float.truncChk a
      unfold op32; generalize Zig.Float.truncChk a = x; rcases x with _ | _ | _ <;> rfl
    | 13, _ =>
      show _ = Zig.Float.roundChk a
      unfold op32; generalize Zig.Float.roundChk a = x; rcases x with _ | _ | _ <;> rfl
    | 16, _ =>
      show _ = Zig.Float.minChk a b
      unfold op32; generalize Zig.Float.minChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 17, _ =>
      show _ = Zig.Float.maxChk a b
      unfold op32; generalize Zig.Float.maxChk a b = x; rcases x with _ | _ | _ <;> rfl
    | n + 26, h => omega

theorem op64_spec (sel : BitVec 8) (a b c : Zig.Float .f64) : op64 sel a b c = opSpec sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op64_other sel h, opSpec_other h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ =>
      show _ = Zig.Float.fmaRtChk a b c
      unfold op64; generalize Zig.Float.fmaRtChk a b c = x; rcases x with _ | _ | _ <;> rfl
    | 7, _ =>
      show _ = Zig.Float.remRtChk a b
      unfold op64; generalize Zig.Float.remRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 8, _ =>
      show _ = Zig.Float.modRtChk a b
      unfold op64; generalize Zig.Float.modRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 10, _ =>
      show _ = Zig.Float.floorChk a
      unfold op64; generalize Zig.Float.floorChk a = x; rcases x with _ | _ | _ <;> rfl
    | 11, _ =>
      show _ = Zig.Float.ceilChk a
      unfold op64; generalize Zig.Float.ceilChk a = x; rcases x with _ | _ | _ <;> rfl
    | 12, _ =>
      show _ = Zig.Float.truncChk a
      unfold op64; generalize Zig.Float.truncChk a = x; rcases x with _ | _ | _ <;> rfl
    | 13, _ =>
      show _ = Zig.Float.roundChk a
      unfold op64; generalize Zig.Float.roundChk a = x; rcases x with _ | _ | _ <;> rfl
    | 16, _ =>
      show _ = Zig.Float.minChk a b
      unfold op64; generalize Zig.Float.minChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 17, _ =>
      show _ = Zig.Float.maxChk a b
      unfold op64; generalize Zig.Float.maxChk a b = x; rcases x with _ | _ | _ <;> rfl
    | n + 26, h => omega

/-- Legacy f80 floor/ceil extend to f128, which misreads a pseudo-denormal's value.
With that noncanonical encoding excluded, every selector has the same spec across versions. -/
theorem op80_spec (sel : BitVec 8) (a b c : Zig.Float .f80)
    (ha : a.isPseudoDenormalF80 = false) : op80 sel a b c = opSpec sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op80_other sel h, opSpec_other h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ =>
      show _ = Zig.Float.fmaRtChk a b c
      unfold op80; generalize Zig.Float.fmaRtChk a b c = x; rcases x with _ | _ | _ <;> rfl
    | 7, _ =>
      show _ = Zig.Float.remRtChk a b
      unfold op80; generalize Zig.Float.remRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 8, _ =>
      show _ = Zig.Float.modRtChk a b
      unfold op80; generalize Zig.Float.modRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 10, _ =>
      show _ = Zig.Float.floorChk a
      unfold op80
      -- Pre-0.16 output uses the legacy wrapper; current output already uses floorChk.
      try rw [Zig.Float.floorRtLegacyChk_eq a ha]
      generalize Zig.Float.floorChk a = x; rcases x with _ | _ | _ <;> rfl
    | 11, _ =>
      show _ = Zig.Float.ceilChk a
      unfold op80
      try rw [Zig.Float.ceilRtLegacyChk_eq a ha]
      generalize Zig.Float.ceilChk a = x; rcases x with _ | _ | _ <;> rfl
    | 12, _ =>
      show _ = Zig.Float.truncChk a
      unfold op80; generalize Zig.Float.truncChk a = x; rcases x with _ | _ | _ <;> rfl
    | 13, _ =>
      show _ = Zig.Float.roundChk a
      unfold op80; generalize Zig.Float.roundChk a = x; rcases x with _ | _ | _ <;> rfl
    | 16, _ =>
      show _ = Zig.Float.minChk a b
      unfold op80; generalize Zig.Float.minChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 17, _ =>
      show _ = Zig.Float.maxChk a b
      unfold op80; generalize Zig.Float.maxChk a b = x; rcases x with _ | _ | _ <;> rfl
    | n + 26, h => omega

/-- `f128`: `/`, `@divTrunc`, `@divFloor` and `@sqrt` (`sel` 3, 5, 6, 9) call another model
function per Zig version (`docs/floats.md` §Per-version differences); every other `sel` is
`opSpec`. -/
theorem op128_spec (sel : BitVec 8) (hs : sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9)
    (a b c : Zig.Float .f128) : op128 sel a b c = opSpec sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op128_other sel h, opSpec_other h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 3, _ => exact absurd rfl hs.1
    | 5, _ => exact absurd rfl hs.2.1
    | 6, _ => exact absurd rfl hs.2.2.1
    | 9, _ => exact absurd rfl hs.2.2.2
    | 0, _ | 1, _ | 2, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ =>
      show _ = Zig.Float.fmaRtChk a b c
      unfold op128; generalize Zig.Float.fmaRtChk a b c = x; rcases x with _ | _ | _ <;> rfl
    | 7, _ =>
      show _ = Zig.Float.remRtChk a b
      unfold op128; generalize Zig.Float.remRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 8, _ =>
      show _ = Zig.Float.modRtChk a b
      unfold op128; generalize Zig.Float.modRtChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 10, _ =>
      show _ = Zig.Float.floorChk a
      unfold op128; generalize Zig.Float.floorChk a = x; rcases x with _ | _ | _ <;> rfl
    | 11, _ =>
      show _ = Zig.Float.ceilChk a
      unfold op128; generalize Zig.Float.ceilChk a = x; rcases x with _ | _ | _ <;> rfl
    | 12, _ =>
      show _ = Zig.Float.truncChk a
      unfold op128; generalize Zig.Float.truncChk a = x; rcases x with _ | _ | _ <;> rfl
    | 13, _ =>
      show _ = Zig.Float.roundChk a
      unfold op128; generalize Zig.Float.roundChk a = x; rcases x with _ | _ | _ <;> rfl
    | 16, _ =>
      show _ = Zig.Float.minChk a b
      unfold op128; generalize Zig.Float.minChk a b = x; rcases x with _ | _ | _ <;> rfl
    | 17, _ =>
      show _ = Zig.Float.maxChk a b
      unfold op128; generalize Zig.Float.maxChk a b = x; rcases x with _ | _ | _ <;> rfl
    | n + 26, h => omega

/-! ### `f128` division and `@sqrt` per Zig version (F05) -/

/-- The compiler-rt helper profile of an `f128` translation (`docs/floats.md` §Per-version
differences): `legacy` is Zig 0.14.1 and 0.15.2, `v016` is Zig 0.16.0. -/
inductive F128Rt where
  | legacy
  | v016
  deriving DecidableEq, Repr

/-- `f128` `/` of a profile. `legacy`: IEEE `Float.div` with a nonzero subnormal quotient
flushed to a signed zero (`Zig.Float.divRt_eq_div_of_not_subnormal`,
`Zig.Float.divRt_of_subnormal`). `v016`: IEEE `Float.div` for a NaN, infinite or zero operand
(`Zig.Float.divRt016_eq_div_of_special`) and for operands whose binary exponents differ by at
least −16381 (`Zig.Float.divRt016_eq_div_of_exp`); else the port of `divtf3.zig`'s subnormal
path. -/
def F128Rt.div : F128Rt → Zig.F128 → Zig.F128 → Zig.F128
  | .legacy => Zig.Float.divRt
  | .v016 => Zig.Float.divRt016

/-- `f128` `@sqrt` of a profile. `legacy`: the `f64` root, extended back
(`Zig.Float.sqrtF128ViaF64`; IEEE `Float.sqrt` for a NaN, infinite or zero operand:
`Zig.sqrtF128ViaF64_eq_sqrt_of_special`). `v016`: IEEE `Float.sqrt`. -/
def F128Rt.sqrt : F128Rt → Zig.F128 → Zig.F128
  | .legacy => Zig.Float.sqrtF128ViaF64
  | .v016 => Zig.Float.sqrt

/-- The `f128` op that `sel` picks for a profile: `opSpec`, except the division family and
`@sqrt` (`sel` 3, 5, 6, 9), which use the profile's helpers. -/
def opSpec128 (rt : F128Rt) (sel : BitVec 8) (a b c : Zig.F128) : Zig.Result Zig.F128 :=
  match sel.toNat with
  | 3 => pure (rt.div a b)
  | 5 => pure (Zig.Float.trunc (rt.div a b))
  | 6 => pure (Zig.Float.floor (rt.div a b))
  | 9 => pure (rt.sqrt a)
  | _ => opSpec sel a b c

/-- The profile of the translation in `Gen.lean`: an alternative elaborates only when `op128`'s
division and `@sqrt` selectors are that profile's helpers, checked by `rfl`. The 0.16.0
translation gives `v016`, the 0.14.1 and 0.15.2 translations give `legacy`; any other
translation fails to elaborate. -/
def op128Profile : F128Rt := by
  first
  | exact (fun (_ : ∀ a b c, op128 3 a b c = pure (Zig.Float.divRt016 a b))
        (_ : ∀ a b c, op128 9 a b c = pure (Zig.Float.sqrt a)) => F128Rt.v016)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  | exact (fun (_ : ∀ a b c, op128 3 a b c = pure (Zig.Float.divRt a b))
        (_ : ∀ a b c, op128 9 a b c = pure (Zig.Float.sqrtF128ViaF64 a)) => F128Rt.legacy)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem opSpec128_of_ne (rt : F128Rt) {sel : BitVec 8}
    (hs : sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9) (a b c : Zig.F128) :
    opSpec128 rt sel a b c = opSpec sel a b c := by
  have hne : ∀ k : BitVec 8, sel ≠ k → sel.toNat ≠ k.toNat := fun k hk h =>
    hk (BitVec.eq_of_toNat_eq h)
  have h3 := hne 3 hs.1
  have h5 := hne 5 hs.2.1
  have h6 := hne 6 hs.2.2.1
  have h9 := hne 9 hs.2.2.2
  unfold opSpec128
  split <;> simp_all

/-- `f128`, every selector: `op128` is `opSpec128` of the translation's profile. With
`op128Profile = .v016` (0.16.0) division is `Zig.Float.divRt016` and `@sqrt` is IEEE; with
`.legacy` (0.14.1, 0.15.2) division is `Zig.Float.divRt` and `@sqrt` is
`Zig.Float.sqrtF128ViaF64`. -/
theorem op128_spec_full (sel : BitVec 8) (a b c : Zig.Float .f128) :
    op128 sel a b c = opSpec128 op128Profile sel a b c := by
  by_cases hs : sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9
  · rw [op128_spec sel hs, opSpec128_of_ne _ hs]
  · by_cases h3 : sel = 3
    · subst h3; rfl
    by_cases h5 : sel = 5
    · subst h5; rfl
    by_cases h6 : sel = 6
    · subst h6; rfl
    by_cases h9 : sel = 9
    · subst h9; rfl
    exact absurd ⟨h3, h5, h6, h9⟩ hs

/-- `f128` on every Zig version: with a NaN, infinite or zero `a` (no finite class with a
nonzero mantissa) every selector is `opSpec`, i.e. IEEE division and `@sqrt`; with such a `b`
every selector except `@sqrt` is. The two division profiles and the legacy `@sqrt` differ from
IEEE only on finite nonzero operands. -/
theorem op128_eq_opSpec_of_special (sel : BitVec 8) (a b c : Zig.Float .f128)
    (h : (∀ s m e, a.classify = .finite s m e → m = 0) ∨
      ((∀ s m e, b.classify = .finite s m e → m = 0) ∧ sel ≠ 9)) :
    op128 sel a b c = opSpec sel a b c := by
  have hdiv : ∀ rt : F128Rt, rt.div a b = Zig.Float.div a b := by
    have h' := h.imp_right And.left
    intro rt; cases rt
    · exact Zig.Float.divRt_eq_div_of_special h'
    · exact Zig.Float.divRt016_eq_div_of_special h'
  rw [op128_spec_full]
  by_cases hs : sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9
  · exact opSpec128_of_ne _ hs a b c
  by_cases h3 : sel = 3
  · subst h3; show pure _ = pure _; rw [hdiv]
  by_cases h5 : sel = 5
  · subst h5; show pure _ = pure _; rw [hdiv]
  by_cases h6 : sel = 6
  · subst h6; show pure _ = pure _; rw [hdiv]
  by_cases h9 : sel = 9
  · subst h9
    have ha := h.resolve_right (fun hb => hb.2 rfl)
    show pure _ = pure _
    cases op128Profile
    · exact congrArg pure (Zig.sqrtF128ViaF64_eq_sqrt_of_special ha)
    · rfl
  exact absurd ⟨h3, h5, h6, h9⟩ hs

/-- `@divExact` on `f64`: the quotient rounded and truncated (`docs/floats.md` §Semantics); the
safety check panics if it is not a whole number, so a NaN quotient panics too. -/
theorem divExact64_spec (a b : Zig.F64) :
    divExact64 a b =
      let q := Zig.Float.trunc (Zig.Float.div a b)
      if Zig.Float.eq q (Zig.Float.floor q) then pure q else throw .panic := by
  have hd : Zig.Float.divTruncRt016 a b = Zig.Float.trunc (Zig.Float.div a b) ∧
      Zig.Float.divTruncRt a b = Zig.Float.trunc (Zig.Float.div a b) := ⟨rfl, rfl⟩
  unfold divExact64
  simp only [hd.1, hd.2]
  generalize Zig.Float.trunc (Zig.Float.div a b) = q
  show _ = if Zig.Float.eq q (Zig.Float.floor q) then pure q else throw Zig.Error.panic
  generalize hb : Zig.Float.eq q (Zig.Float.floor q) = t
  cases t <;> simp only [Zig.Float.floorChk, Zig.Float.isInvalidF80, Bool.false_eq_true,
    ↓reduceIte, zig_unfold, hb] <;> rfl
