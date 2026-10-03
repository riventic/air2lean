import Proofs.Floatops.Gen

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
