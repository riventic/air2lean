import Proofs.Floatops.Gen

/-!
# Proofs about `examples/floatops/floatops.zig`

`floatops` is a test bench: `opN` dispatches on `sel` to one float op, and the diff test checks
each op against the compiled Zig bit for bit. The proofs here state what does not depend on the
Zig version: the division selectors (3, 5, 6) call a different model function per version
(`docs/floats.md` §Per-version differences), and CI builds these proofs against each version's
translation.

- `opN_basic`: `sel` 0, 1, 2, 14, 15 are `+`, `-`, `*`, `@abs`, negation.
- `opN_other`: a `sel` of 26 or more returns `a` unchanged.
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

theorem op16_basic (a b c : Zig.Float .f16) :
    op16 0 a b c = pure (Zig.Float.add a b) ∧ op16 1 a b c = pure (Zig.Float.sub a b) ∧
      op16 2 a b c = pure (Zig.Float.mul a b) ∧ op16 14 a b c = pure (Zig.Float.abs a) ∧
      op16 15 a b c = pure (Zig.Float.neg a) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

theorem op32_basic (a b c : Zig.F32) :
    op32 0 a b c = pure (Zig.Float.add a b) ∧ op32 1 a b c = pure (Zig.Float.sub a b) ∧
      op32 2 a b c = pure (Zig.Float.mul a b) ∧ op32 14 a b c = pure (Zig.Float.abs a) ∧
      op32 15 a b c = pure (Zig.Float.neg a) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

theorem op64_basic (a b c : Zig.F64) :
    op64 0 a b c = pure (Zig.Float.add a b) ∧ op64 1 a b c = pure (Zig.Float.sub a b) ∧
      op64 2 a b c = pure (Zig.Float.mul a b) ∧ op64 14 a b c = pure (Zig.Float.abs a) ∧
      op64 15 a b c = pure (Zig.Float.neg a) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

theorem op80_basic (a b c : Zig.Float .f80) :
    op80 0 a b c = pure (Zig.Float.add a b) ∧ op80 1 a b c = pure (Zig.Float.sub a b) ∧
      op80 2 a b c = pure (Zig.Float.mul a b) ∧ op80 14 a b c = pure (Zig.Float.abs a) ∧
      op80 15 a b c = pure (Zig.Float.neg a) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

theorem op128_basic (a b c : Zig.Float .f128) :
    op128 0 a b c = pure (Zig.Float.add a b) ∧ op128 1 a b c = pure (Zig.Float.sub a b) ∧
      op128 2 a b c = pure (Zig.Float.mul a b) ∧ op128 14 a b c = pure (Zig.Float.abs a) ∧
      op128 15 a b c = pure (Zig.Float.neg a) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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
