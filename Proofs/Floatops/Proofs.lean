import Proofs.Floatops.Gen
import ZigLean.Float.RoundTrip
import ZigLean.Witness

/-!
# Proofs about `examples/floatops/floatops.zig`

`floatops` is a test bench: `opN` dispatches on `sel` to one float op, and the diff test checks
each op against the compiled Zig bit for bit. CI builds these proofs against each Zig version's
translation on each declared target, so every statement holds for each of them. Where the
versions differ (`f128` division and `@sqrt`, `docs/floats.md` §Per-version differences) the
statement names the translation's profile; where the targets differ (`@mulAdd`, `f80`,
§Targets) it names the translation's target (`floatopsTarget`).

- `opN_spec`: every `sel` picks its op (`opSpec floatopsTarget`). `/`, `@divTrunc` and
  `@divFloor` are `Float.div` on every version and target for `f16`..`f64`; `op128_spec` leaves
  out `sel` 3, 5, 6, 9 (`f128` division and `@sqrt` differ by version). Multiplication and
  remainder use the compiler-rt helpers selected by this example; `@mulAdd` is the target's
  (`FloatTarget.fmaRt`). `opN_other`: a `sel` of 26 or more returns `a` unchanged.
- `f80` differs by target (`docs/floats.md` §Targets): `op80_spec` (premise
  `floatopsTarget = .x86_64`, the x87) is `opSpec`, and excludes a pseudo-denormal numerator
  because f80 floor/ceil changed in 0.16.0 and f80 trunc in 0.17.0 (`docs/floats.md` groups H
  and I); `op80_spec_aarch64` (premise `.aarch64`, soft float)
  is `opSpec80A64`: `.unspecified` on a noncanonical operand, `__divxf3` division, and before
  0.16.0 `@sqrt` through `f64`.
- `op128_spec_full`: every `sel` of `op128` is `opSpec128 floatopsTarget op128Profile`: the
  division family and `@sqrt` use the helpers of the translation's profile (`F128Rt.legacy` for
  0.14.1 and 0.15.2, `F128Rt.v016` for 0.16.0), whose specifications against IEEE are in
  `ZigLean/Float/CompilerRt.lean` and `ZigLean/Float/RoundTrip.lean`.
  `op128_eq_opSpec_of_special`: on every version, a NaN, infinite or zero `a` (or `b`, except
  for `@sqrt`) gives `opSpec`, the IEEE result.
- `divExact64_spec`: the truncated quotient; `.illegal` for an inexact quotient that is not
  NaN, and a panic (the safety check) for a NaN one.
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

/-! ### Profiles of the translation

CI builds these proofs against the translation of every Zig version on x86_64-linux, and of
0.16.0 and 0.15.2 on aarch64-macos (`docs/target-matrix.md`). `floatopsTarget` and
`op128Profile` read the translation's target and version off `Gen.lean`; a statement that holds
for one target only takes `floatopsTarget = …` as a premise. -/

/-- The float target of a translation (`docs/floats.md` §Targets): the architecture of the
profile's `target_triple`. A legacy profile is x86_64. -/
inductive FloatTarget where
  | x86_64
  | aarch64
  deriving DecidableEq, Repr

/-- `@mulAdd` in `compiler-rt` mode on a target: x86_64 calls compiler_rt for every format
(group B, `Zig.Float.fmaRtChk`); aarch64 has a fused instruction for `f16`/`f32`/`f64` and calls
compiler_rt for `f80`/`f128` (`Zig.Float.fmaRtFused`). -/
def FloatTarget.fmaRt {fmt : Zig.FloatFmt} :
    FloatTarget → Zig.Float fmt → Zig.Float fmt → Zig.Float fmt → Zig.Result (Zig.Float fmt)
  | .x86_64, a, b, c => Zig.Float.fmaRtChk a b c
  | .aarch64, a, b, c => pure (Zig.Float.fmaRtFused a b c)

/-- The target of the translation in `Gen.lean`: an alternative elaborates only when `op80`'s
addition (x86_64: the x87 `Float.add`) or `op64`'s `@mulAdd` (aarch64: the fused instruction)
is that target's, checked by `rfl`. -/
def floatopsTarget : FloatTarget := by
  first
  | exact (fun (_ : ∀ a b c, op80 0 a b c = pure (Zig.Float.add a b)) => FloatTarget.x86_64)
      (fun _ _ _ => rfl)
  | exact (fun (_ : ∀ a b c, op64 4 a b c = pure (Zig.Float.fmaRtFused a b c)) =>
        FloatTarget.aarch64)
      (fun _ _ _ => rfl)

/-- `opN`'s branch for one selector binds the result `X`: generalize it and compute. -/
local macro "spec_case " f:ident ", " X:term : tactic =>
  `(tactic| (show _ = $X; unfold $f:ident; generalize $X = x; rcases x with _ | _ | _ <;> rfl))

/-- The compiler-rt helper profile of a translation (`docs/floats.md` §Per-version
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

/-- aarch64 `f80` `@sqrt` of a profile: `legacy`'s soft-float `__sqrtx` rounds through `f64`
(`Zig.Float.sqrtF80ViaF64`); `v016`'s is correctly rounded. -/
def F128Rt.sqrt80 : F128Rt → Zig.F80 → Zig.F80
  | .legacy => Zig.Float.sqrtF80ViaF64
  | .v016 => Zig.Float.sqrt

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

/-! ### Every selector -/

/-- The op that `sel` picks on a target, in the model (`docs/floats.md` §Semantics). `/`,
`@divTrunc` and `@divFloor` are `Float.div` then `trunc`/`floor`: on `f16`..`f64` that is the
model of every Zig version and target, on `f80` of x86_64 (aarch64: `opSpec80A64`). The
targets differ only in `@mulAdd` (`FloatTarget.fmaRt`). -/
def opSpec {fmt : Zig.FloatFmt} (t : FloatTarget) (sel : BitVec 8) (a b c : Zig.Float fmt) :
    Zig.Result (Zig.Float fmt) :=
  match sel.toNat with
  | 0 => pure (Zig.Float.add a b)
  | 1 => pure (Zig.Float.sub a b)
  | 2 => pure (Zig.Float.mulRt a b)
  | 3 => pure (Zig.Float.div a b)
  | 4 => t.fmaRt a b c
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

theorem opSpec_other {fmt : Zig.FloatFmt} (t : FloatTarget) {sel : BitVec 8}
    (h : 26 ≤ sel.toNat) (a b c : Zig.Float fmt) : opSpec t sel a b c = pure a := by
  unfold opSpec
  split <;> first | omega | rfl

/-- A `sel` below 26 is `BitVec.ofNat 8 n` for an `n` below 26. -/
theorem sel_lt {sel : BitVec 8} (h : ¬26 ≤ sel.toNat) :
    ∃ n, n < 26 ∧ sel = BitVec.ofNat 8 n :=
  ⟨sel.toNat, by omega, by simp⟩

/-- The `@mulAdd` selector of `opN` for the translation's target. -/
local macro "fma_case " f:ident : tactic =>
  `(tactic| (
    show _ = floatopsTarget.fmaRt _ _ _
    cases ht : floatopsTarget
    · first | exact absurd ht (by decide) | spec_case $f, Zig.Float.fmaRtChk _ _ _
    · first | exact absurd ht (by decide) | rfl))

theorem op16_spec (sel : BitVec 8) (a b c : Zig.Float .f16) :
    op16 sel a b c = opSpec floatopsTarget sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op16_other sel h, opSpec_other _ h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ => fma_case op16
    | 7, _ => spec_case op16, Zig.Float.remRtChk a b
    | 8, _ => spec_case op16, Zig.Float.modRtChk a b
    | 10, _ => spec_case op16, Zig.Float.floorChk a
    | 11, _ => spec_case op16, Zig.Float.ceilChk a
    | 12, _ => spec_case op16, Zig.Float.truncChk a
    | 13, _ => spec_case op16, Zig.Float.roundChk a
    | 16, _ => spec_case op16, Zig.Float.minChk a b
    | 17, _ => spec_case op16, Zig.Float.maxChk a b
    | n + 26, h => omega

theorem op32_spec (sel : BitVec 8) (a b c : Zig.Float .f32) :
    op32 sel a b c = opSpec floatopsTarget sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op32_other sel h, opSpec_other _ h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ => fma_case op32
    | 7, _ => spec_case op32, Zig.Float.remRtChk a b
    | 8, _ => spec_case op32, Zig.Float.modRtChk a b
    | 10, _ => spec_case op32, Zig.Float.floorChk a
    | 11, _ => spec_case op32, Zig.Float.ceilChk a
    | 12, _ => spec_case op32, Zig.Float.truncChk a
    | 13, _ => spec_case op32, Zig.Float.roundChk a
    | 16, _ => spec_case op32, Zig.Float.minChk a b
    | 17, _ => spec_case op32, Zig.Float.maxChk a b
    | n + 26, h => omega

theorem op64_spec (sel : BitVec 8) (a b c : Zig.Float .f64) :
    op64 sel a b c = opSpec floatopsTarget sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op64_other sel h, opSpec_other _ h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ => fma_case op64
    | 7, _ => spec_case op64, Zig.Float.remRtChk a b
    | 8, _ => spec_case op64, Zig.Float.modRtChk a b
    | 10, _ => spec_case op64, Zig.Float.floorChk a
    | 11, _ => spec_case op64, Zig.Float.ceilChk a
    | 12, _ => spec_case op64, Zig.Float.truncChk a
    | 13, _ => spec_case op64, Zig.Float.roundChk a
    | 16, _ => spec_case op64, Zig.Float.minChk a b
    | 17, _ => spec_case op64, Zig.Float.maxChk a b
    | n + 26, h => omega

/-- x86_64 `f80` (the x87): every selector is `opSpec`. Legacy f80 floor/ceil extend to f128,
which misreads a pseudo-denormal's value; with that noncanonical encoding excluded, every
selector has the same spec across versions. -/
theorem op80_spec (ht : floatopsTarget = .x86_64) (sel : BitVec 8) (a b c : Zig.Float .f80)
    (ha : a.isPseudoDenormalF80 = false) : op80 sel a b c = opSpec .x86_64 sel a b c := by
  first
  | exact absurd ht (by decide)
  | by_cases h : 26 ≤ sel.toNat
    · rw [op80_other sel h, opSpec_other _ h]
    · obtain ⟨n, hn, rfl⟩ := sel_lt h
      match n, hn with
      | 0, _ | 1, _ | 2, _ | 3, _ | 5, _ | 6, _ | 9, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
      | 4, _ => spec_case op80, Zig.Float.fmaRtChk a b c
      | 7, _ => spec_case op80, Zig.Float.remRtChk a b
      | 8, _ => spec_case op80, Zig.Float.modRtChk a b
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
        unfold op80
        -- 0.17.0 output keeps a zero-extension pseudo-denormal (`truncRt017Chk`, group I).
        try rw [Zig.Float.truncRt017Chk_eq a ha]
        generalize Zig.Float.truncChk a = x; rcases x with _ | _ | _ <;> rfl
      | 13, _ => spec_case op80, Zig.Float.roundChk a
      | 16, _ => spec_case op80, Zig.Float.minChk a b
      | 17, _ => spec_case op80, Zig.Float.maxChk a b
      | n + 26, h => omega

/-- The `f80` operands that `op80`'s selector reads on aarch64: every op except the sign-bit ops
(`@abs`, `-x`) and an unlisted `sel` calls a soft-float routine on them. -/
def f80Reads (sel : BitVec 8) (a b c : Zig.F80) : List Zig.F80 :=
  match sel.toNat with
  | 4 => [a, b, c]
  | 0 | 1 | 2 | 3 | 5 | 6 | 7 | 8 | 16 | 17 => [a, b]
  | 14 | 15 => []
  | n => if n < 26 then [a] else []

/-- aarch64 `f80` (soft float, `docs/floats.md` §Targets): `opSpec` under
`Zig.Float.softF80Chk` of the operands the selector reads, except that `/`, `@divTrunc` and
`@divFloor` use `__divxf3` (`Zig.Float.divXf3`) and, before 0.16.0, `@sqrt` rounds through
`f64` (`F128Rt.sqrt80`). -/
def opSpec80A64 (rt : F128Rt) (sel : BitVec 8) (a b c : Zig.F80) : Zig.Result Zig.F80 :=
  Zig.Float.softF80Chk (f80Reads sel a b c) <|
    match sel.toNat with
    | 3 => pure (Zig.Float.divXf3 a b)
    | 5 => pure (Zig.Float.divTruncXf3 a b)
    | 6 => pure (Zig.Float.divFloorXf3 a b)
    | 9 => pure (rt.sqrt80 a)
    | _ => opSpec .aarch64 sel a b c

/-- `softF80Chk` excludes a pseudo-denormal, so the legacy floor/ceil wrappers agree with the
current ones under it. -/
theorem softF80Chk_floorRtLegacy (a : Zig.F80) :
    Zig.Float.softF80Chk [a] (Zig.Float.floorRtLegacyChk a) =
      Zig.Float.softF80Chk [a] (Zig.Float.floorChk a) := by
  unfold Zig.Float.softF80Chk
  cases h : a.isPseudoDenormalF80
  · rw [Zig.Float.floorRtLegacyChk_eq a h]
  · simp [Zig.Float.isNoncanonicalF80, h]

theorem softF80Chk_ceilRtLegacy (a : Zig.F80) :
    Zig.Float.softF80Chk [a] (Zig.Float.ceilRtLegacyChk a) =
      Zig.Float.softF80Chk [a] (Zig.Float.ceilChk a) := by
  unfold Zig.Float.softF80Chk
  cases h : a.isPseudoDenormalF80
  · rw [Zig.Float.ceilRtLegacyChk_eq a h]
  · simp [Zig.Float.isNoncanonicalF80, h]

/-- The same for 0.17.0's f80 `@trunc` (`truncRt017Chk`, group I). -/
theorem softF80Chk_truncRt017 (a : Zig.F80) :
    Zig.Float.softF80Chk [a] (Zig.Float.truncRt017Chk a) =
      Zig.Float.softF80Chk [a] (Zig.Float.truncChk a) := by
  unfold Zig.Float.softF80Chk
  cases h : a.isPseudoDenormalF80
  · rw [Zig.Float.truncRt017Chk_eq a h]
  · simp [Zig.Float.isNoncanonicalF80, h]

/-- aarch64 `f80`: every selector is `opSpec80A64` of the translation's version profile. -/
theorem op80_spec_aarch64 (ht : floatopsTarget = .aarch64) (sel : BitVec 8)
    (a b c : Zig.Float .f80) : op80 sel a b c = opSpec80A64 op128Profile sel a b c := by
  first
  | exact absurd ht (by decide)
  | by_cases h : 26 ≤ sel.toNat
    · rw [op80_other sel h]
      have hr : f80Reads sel a b c = [] := by
        unfold f80Reads
        split
        all_goals first | omega | rfl | exact if_neg (by omega)
      unfold opSpec80A64
      simp only [hr, Zig.Float.softF80Chk, List.any_nil, Bool.false_eq_true, ite_false]
      split <;> first | omega | exact (opSpec_other _ h a b c).symm
    · obtain ⟨n, hn, rfl⟩ := sel_lt h
      match n, hn with
      | 14, _ | 15, _ => rfl
      | 0, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (pure (Zig.Float.add a b))
      | 1, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (pure (Zig.Float.sub a b))
      | 2, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (pure (Zig.Float.mulRt a b))
      | 3, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (pure (Zig.Float.divXf3 a b))
      | 4, _ =>
        spec_case op80, Zig.Float.softF80Chk [a, b, c] (pure (Zig.Float.fmaRtFused a b c))
      | 5, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (pure (Zig.Float.divTruncXf3 a b))
      | 6, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (pure (Zig.Float.divFloorXf3 a b))
      | 7, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (Zig.Float.remRtChk a b)
      | 8, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (Zig.Float.modRtChk a b)
      | 9, _ =>
        first
        | spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.sqrt a))
        | spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.sqrtF80ViaF64 a))
      | 10, _ =>
        show _ = Zig.Float.softF80Chk [a] (Zig.Float.floorChk a)
        unfold op80
        try rw [softF80Chk_floorRtLegacy a]
        generalize Zig.Float.softF80Chk [a] (Zig.Float.floorChk a) = x
        rcases x with _ | _ | _ <;> rfl
      | 11, _ =>
        show _ = Zig.Float.softF80Chk [a] (Zig.Float.ceilChk a)
        unfold op80
        try rw [softF80Chk_ceilRtLegacy a]
        generalize Zig.Float.softF80Chk [a] (Zig.Float.ceilChk a) = x
        rcases x with _ | _ | _ <;> rfl
      | 12, _ =>
        show _ = Zig.Float.softF80Chk [a] (Zig.Float.truncChk a)
        unfold op80
        try rw [softF80Chk_truncRt017 a]
        generalize Zig.Float.softF80Chk [a] (Zig.Float.truncChk a) = x
        rcases x with _ | _ | _ <;> rfl
      | 13, _ => spec_case op80, Zig.Float.softF80Chk [a] (Zig.Float.roundChk a)
      | 16, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (Zig.Float.minChk a b)
      | 17, _ => spec_case op80, Zig.Float.softF80Chk [a, b] (Zig.Float.maxChk a b)
      | 18, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .sin a))
      | 19, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .cos a))
      | 20, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .tan a))
      | 21, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .exp a))
      | 22, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .exp2 a))
      | 23, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .log a))
      | 24, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .log2 a))
      | 25, _ => spec_case op80, Zig.Float.softF80Chk [a] (pure (Zig.Float.libm .log10 a))
      | n + 26, h => omega

/-- `f128`: `/`, `@divTrunc`, `@divFloor` and `@sqrt` (`sel` 3, 5, 6, 9) call another model
function per Zig version (`docs/floats.md` §Per-version differences); every other `sel` is
`opSpec` of the translation's target. -/
theorem op128_spec (sel : BitVec 8) (hs : sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9)
    (a b c : Zig.Float .f128) : op128 sel a b c = opSpec floatopsTarget sel a b c := by
  by_cases h : 26 ≤ sel.toNat
  · rw [op128_other sel h, opSpec_other _ h]
  · obtain ⟨n, hn, rfl⟩ := sel_lt h
    match n, hn with
    | 3, _ => exact absurd rfl hs.1
    | 5, _ => exact absurd rfl hs.2.1
    | 6, _ => exact absurd rfl hs.2.2.1
    | 9, _ => exact absurd rfl hs.2.2.2
    | 0, _ | 1, _ | 2, _ | 14, _ | 15, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ => rfl
    | 4, _ => fma_case op128
    | 7, _ => spec_case op128, Zig.Float.remRtChk a b
    | 8, _ => spec_case op128, Zig.Float.modRtChk a b
    | 10, _ => spec_case op128, Zig.Float.floorChk a
    | 11, _ => spec_case op128, Zig.Float.ceilChk a
    | 12, _ => spec_case op128, Zig.Float.truncChk a
    | 13, _ => spec_case op128, Zig.Float.roundChk a
    | 16, _ => spec_case op128, Zig.Float.minChk a b
    | 17, _ => spec_case op128, Zig.Float.maxChk a b
    | n + 26, h => omega

/-! ### `f128` division and `@sqrt` per Zig version (F05) -/

/-- The `f128` op that `sel` picks for a target and profile: `opSpec`, except the division
family and `@sqrt` (`sel` 3, 5, 6, 9), which use the profile's helpers. -/
def opSpec128 (t : FloatTarget) (rt : F128Rt) (sel : BitVec 8) (a b c : Zig.F128) :
    Zig.Result Zig.F128 :=
  match sel.toNat with
  | 3 => pure (rt.div a b)
  | 5 => pure (Zig.Float.trunc (rt.div a b))
  | 6 => pure (Zig.Float.floor (rt.div a b))
  | 9 => pure (rt.sqrt a)
  | _ => opSpec t sel a b c

theorem opSpec128_of_ne (t : FloatTarget) (rt : F128Rt) {sel : BitVec 8}
    (hs : sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9) (a b c : Zig.F128) :
    opSpec128 t rt sel a b c = opSpec t sel a b c := by
  have hne : ∀ k : BitVec 8, sel ≠ k → sel.toNat ≠ k.toNat := fun k hk h =>
    hk (BitVec.eq_of_toNat_eq h)
  have h3 := hne 3 hs.1
  have h5 := hne 5 hs.2.1
  have h6 := hne 6 hs.2.2.1
  have h9 := hne 9 hs.2.2.2
  unfold opSpec128
  split <;> simp_all

/-- A selector is outside the division family and `@sqrt`, or one of them. -/
theorem sel_cases128 (sel : BitVec 8) :
    (sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9) ∨ sel = 3 ∨ sel = 5 ∨ sel = 6 ∨ sel = 9 := by
  by_cases h3 : sel = 3
  · exact .inr (.inl h3)
  by_cases h5 : sel = 5
  · exact .inr (.inr (.inl h5))
  by_cases h6 : sel = 6
  · exact .inr (.inr (.inr (.inl h6)))
  by_cases h9 : sel = 9
  · exact .inr (.inr (.inr (.inr h9)))
  exact .inl ⟨h3, h5, h6, h9⟩

/-- `f128`, every selector: `op128` is `opSpec128` of the translation's target and profile.
With `op128Profile = .v016` (0.16.0) division is `Zig.Float.divRt016` and `@sqrt` is IEEE; with
`.legacy` (0.14.1, 0.15.2) division is `Zig.Float.divRt` and `@sqrt` is
`Zig.Float.sqrtF128ViaF64`. -/
theorem op128_spec_full (sel : BitVec 8) (a b c : Zig.Float .f128) :
    op128 sel a b c = opSpec128 floatopsTarget op128Profile sel a b c := by
  rcases sel_cases128 sel with hs | rfl | rfl | rfl | rfl
  · rw [op128_spec sel hs, opSpec128_of_ne _ _ hs]
  all_goals rfl

/-- `f128` on every Zig version and target: with a NaN, infinite or zero `a` (no finite class
with a nonzero mantissa) every selector is `opSpec`, i.e. IEEE division and `@sqrt`; with such
a `b` every selector except `@sqrt` is. The two division profiles and the legacy `@sqrt` differ
from IEEE only on finite nonzero operands. -/
theorem op128_eq_opSpec_of_special (sel : BitVec 8) (a b c : Zig.Float .f128)
    (h : (∀ s m e, a.classify = .finite s m e → m = 0) ∨
      ((∀ s m e, b.classify = .finite s m e → m = 0) ∧ sel ≠ 9)) :
    op128 sel a b c = opSpec floatopsTarget sel a b c := by
  have hdiv : ∀ rt : F128Rt, rt.div a b = Zig.Float.div a b := by
    have h' := h.imp_right And.left
    intro rt; cases rt
    · exact Zig.Float.divRt_eq_div_of_special h'
    · exact Zig.Float.divRt016_eq_div_of_special h'
  rw [op128_spec_full]
  rcases sel_cases128 sel with hs | rfl | rfl | rfl | rfl
  · exact opSpec128_of_ne _ _ hs a b c
  · show pure _ = pure _; rw [hdiv]
  · show pure _ = pure _; rw [hdiv]
  · show pure _ = pure _; rw [hdiv]
  · have ha := h.resolve_right (fun hb => hb.2 rfl)
    show pure _ = pure _
    cases op128Profile
    · exact congrArg pure (Zig.sqrtF128ViaF64_eq_sqrt_of_special ha)
    · rfl

/-- `@divExact` on `f64`: the quotient rounded and truncated (`docs/floats.md` §Semantics).
An inexact quotient is illegal behaviour (`.illegal`, `docs/illegal-behavior.md`) unless it is
NaN: ReleaseSafe's safety check catches only that one, and panics. -/
theorem divExact64_spec (a b : Zig.F64) :
    divExact64 a b =
      let q := Zig.Float.div a b
      if q.isNaN || Zig.Float.exactQuotient a b q then
        let t := Zig.Float.trunc q
        if Zig.Float.eq t (Zig.Float.floor t) then pure t else throw .panic
      else throw .illegal := by
  have hd : Zig.Float.divRt016 a b = Zig.Float.div a b ∧ Zig.Float.divRt a b = Zig.Float.div a b :=
    ⟨rfl, rfl⟩
  unfold divExact64
  simp only [hd.1, hd.2]
  generalize Zig.Float.div a b = q
  show _ = if q.isNaN || Zig.Float.exactQuotient a b q then
      (if Zig.Float.eq (Zig.Float.trunc q) (Zig.Float.floor (Zig.Float.trunc q)) then
        pure (Zig.Float.trunc q) else throw Zig.Error.panic)
    else throw Zig.Error.illegal
  generalize hx : (q.isNaN || Zig.Float.exactQuotient a b q) = x
  cases x
  · simp only [Zig.Float.divExactTrunc, hx, Bool.false_eq_true, ↓reduceIte, zig_unfold] <;> rfl
  · generalize hb : Zig.Float.eq (Zig.Float.trunc q) (Zig.Float.floor (Zig.Float.trunc q)) = t
    cases t <;> simp only [Zig.Float.divExactTrunc, hx, Zig.Float.floorChk,
      Zig.Float.isInvalidF80, Bool.false_eq_true, ↓reduceIte, zig_unfold, hb] <;> rfl

/-! ## Non-vacuity witnesses: a quiet NaN, the first selector that is not an op -/

nonvacuity_witness cmp64_nan :=
  ⟨Zig.Float.ofBits 0x7ff8000000000000, Zig.Float.ofBits 0, .inl (by decide +kernel), trivial⟩
nonvacuity_witness op16_other := ⟨26, by decide, Zig.Float.ofBits 0, Zig.Float.ofBits 0, Zig.Float.ofBits 0, trivial⟩
nonvacuity_witness op32_other := ⟨26, by decide, Zig.Float.ofBits 0, Zig.Float.ofBits 0, Zig.Float.ofBits 0, trivial⟩
nonvacuity_witness op64_other := ⟨26, by decide, Zig.Float.ofBits 0, Zig.Float.ofBits 0, Zig.Float.ofBits 0, trivial⟩
nonvacuity_witness op80_other := ⟨26, by decide, Zig.Float.ofBits 0, Zig.Float.ofBits 0, Zig.Float.ofBits 0, trivial⟩
nonvacuity_witness op128_other :=
  ⟨26, by decide, Zig.Float.ofBits 0, Zig.Float.ofBits 0, Zig.Float.ofBits 0, trivial⟩
nonvacuity_witness opSpec_other :=
  ⟨.f32, .x86_64, 26, by decide, Zig.Float.ofBits 0, Zig.Float.ofBits 0, Zig.Float.ofBits 0, trivial⟩
