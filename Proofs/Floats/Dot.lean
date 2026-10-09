import ZigLean.Float.Error
import Proofs.Floats.Gen
import ZigLean.Witness

/-!
# Numerical bounds for `dot` (`examples/floats/floats.zig`)

`dot` accumulates `s += x * y` from `s = +0` over two `f64` slices. `dot_eq_sumLeft` turns the
generated loop into the left fold `Zig.Float.sumLeft` of the rounded products, in loop
order. `dot_error` then proves the stated property: for `n` elements with finite values of
magnitude at most `B`, and the explicit overflow precondition `n·c·ρⁿ < 2^1023`
(`c = B²(1 + u) + 2η`, `ρ = 1 + u`, `u = 2^-53`, `η = 2^-1075`), `dot` returns a finite value
of magnitude at most `n·c·ρⁿ` within `n·(u·n·c·ρⁿ + η) + n·(u·B² + η)` of the exact dot
product. `dot_isNaN` is the NaN condition: one NaN element in `xs` makes the result NaN.
`dot_pos_of_gap` is a stable comparison: the result compares above `+0` whenever the exact
dot product exceeds the error bound.

The proofs follow the loop's accumulation order; none reassociates a float sum.
-/

open Floats

local notation "u64" => Zig.FloatFmt.f64.unitRoundoff
local notation "η64" => Zig.FloatFmt.f64.underflowError
local notation "Ω64" => Zig.FloatFmt.f64.overflowBound

/-- The `i`-th rounded product `xs[i] * ys[i]`. -/
def dotTerm (xs ys : Array Zig.F64) (i : Nat) : Zig.F64 := Zig.Float.mul xs[i]! ys[i]!

/-- The loop's partial sum after `k` iterations. -/
def dotAcc (xs ys : Array Zig.F64) (k : Nat) : Zig.F64 :=
  Zig.Float.sumLeft (Zig.Float.ofBits (0 : BitVec 64)) (dotTerm xs ys) k

theorem dot_loop_step (xs ys : Array Zig.F64) (hs : xs.size < 2 ^ 64) (hlen : xs.size = ys.size)
    (s : dotLocals) (hk : s.local4.toNat ≤ xs.size) (ht : s.s = dotAcc xs ys s.local4.toNat) :
    ∃ e s', (dot.loop15 xs ys (Zig.len xs)).run s = pure (e, s') ∧
      (if dot.again15 e then
          (s'.local4.toNat ≤ xs.size ∧ s'.s = dotAcc xs ys s'.local4.toNat) ∧
            xs.size - s'.local4.toNat < xs.size - s.local4.toNat
        else e = .br14 ∧ s'.s = dotAcc xs ys xs.size) := by
  unfold dot.loop15
  have hm : xs.size % 18446744073709551616 = xs.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : s.local4.toNat < xs.size
  · have hlt' : s.local4.toNat < ys.size := hlen ▸ hlt
    have hinc : ¬ 18446744073709551615 ≤ s.local4.toNat := by omega
    refine ⟨.rep15, ⟨Zig.Float.add s.s
      (Zig.Float.mul (xs[s.local4.toNat]'hlt) (ys[s.local4.toNat]'hlt')), s.local4 + 1⟩, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hlt', hm, hinc, StateT.lift]
    · have h5 : (s.local4 + 1).toNat = s.local4.toNat + 1 := Zig.toNat_add_one _ (by omega)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h5]; omega
      · rw [h5, ht]
        simp [dotAcc, Zig.Float.sumLeft, dotTerm, hlt, hlt']
      · rw [h5]; omega
  · have heq : s.local4.toNat = xs.size := by omega
    refine ⟨.br14, s, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm]
    · simp only [dot.again15, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, heq ▸ ht⟩

/-- `dot` of two equal-length slices is the left fold of the rounded products from `+0`, in
loop order. -/
theorem dot_eq_sumLeft (xs ys : Array Zig.F64) (hs : xs.size < 2 ^ 64) (hlen : xs.size = ys.size) :
    dot xs ys = pure (dotAcc xs ys xs.size) := by
  obtain ⟨⟨e, s'⟩, hrun, he, hpost⟩ := Zig.loop_spec (dot.loop15 xs ys (Zig.len xs))
    dot.again15
    (fun s => s.local4.toNat ≤ xs.size ∧ s.s = dotAcc xs ys s.local4.toNat)
    (fun s => xs.size - s.local4.toNat)
    (fun r => r.1 = .br14 ∧ r.2.s = dotAcc xs ys xs.size)
    (fun s hs' => dot_loop_step xs ys hs hlen s hs'.1 hs'.2)
    { s := Zig.Float.ofBits (0 : BitVec 64), local4 := 0 } (by simp [dotAcc, Zig.Float.sumLeft])
  subst he
  have hne : (Zig.len xs = Zig.len ys) = True := eq_true (by simp [Zig.len, hlen])
  unfold dot
  change Zig.loop (dot.loop15 xs ys (Zig.len xs)) dot.again15
    { s := Zig.Float.ofBits 0#64, local4 := 0#64 } = some (Except.ok (dotExit.br14, s'))
    at hrun
  simp only at hpost
  simp [zig_unfold, hne, StateT.bind, hrun, hpost]

/-- The `f64` zero `dot` starts from has the exact value `0`. -/
theorem dot_init_toRat : (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64).toRat? = some 0 := by
  rw [show (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) = Zig.Float.zero false by decide]
  simp [Zig.Float.toRat?, Zig.classify_zero, Zig.finiteToRat_zero]

/-- `|a·b| ≤ B²` for `|a|, |b| ≤ B`. -/
private theorem mul_bound {a b B : Rat} (ha : -B ≤ a ∧ a ≤ B) (hb : -B ≤ b ∧ b ≤ B) :
    -(B * B) ≤ a * b ∧ a * b ≤ B * B := by
  have h1 := Rat.mul_nonneg (show 0 ≤ B - a by grind) (show 0 ≤ B - b by grind)
  have h2 := Rat.mul_nonneg (show 0 ≤ B + a by grind) (show 0 ≤ B + b by grind)
  have h3 := Rat.mul_nonneg (show 0 ≤ B - a by grind) (show 0 ≤ B + b by grind)
  have h4 := Rat.mul_nonneg (show 0 ≤ B + a by grind) (show 0 ≤ B - b by grind)
  constructor <;> grind

/-- One rounded product of `dot`: finite, within `u·B² + η` of the exact product, and of
magnitude at most `B²(1 + u) + η`, when `B² < 2^1023`. -/
theorem dotTerm_error (xs ys : Array Zig.F64) {i : Nat} (hi : i < xs.size) (hi' : i < ys.size)
    {a b B : Rat} (hx : xs[i].toRat? = some a ∧ -B ≤ a ∧ a ≤ B)
    (hy : ys[i].toRat? = some b ∧ -B ≤ b ∧ b ≤ B) (hov : B * B < Ω64) :
    ∃ v, (dotTerm xs ys i).toRat? = some v ∧
      v - a * b ≤ u64 * (B * B) + η64 ∧ a * b - v ≤ u64 * (B * B) + η64 ∧
      -(B * B * (1 + u64) + η64) ≤ v ∧ v ≤ B * B * (1 + u64) + η64 := by
  obtain ⟨hlo, hhi⟩ := mul_bound hx.2 hy.2
  obtain ⟨v, hv, e1, e2⟩ := Zig.mul_error hx.1 hy.1 hlo hhi hov
  refine ⟨v, ?_, e1, e2, ?_, ?_⟩
  · simp only [dotTerm, getElem!_pos xs i hi, getElem!_pos ys i hi']
    exact hv
  all_goals grind

/-- **Numerical property of `dot`.** For `n` equal-length elements whose values are finite
with magnitude at most `B`, under the overflow precondition `n·c·ρⁿ < 2^1023`
(`c = B²(1 + u) + 2η`, `ρ = 1 + u`): `dot` returns a finite value `q` (no NaN, no infinity,
no panic) with `|q| ≤ n·c·ρⁿ`, within `n·(u·n·c·ρⁿ + η) + n·(u·B² + η)` of the exact
`∑ a i * b i`. -/
theorem dot_error (xs ys : Array Zig.F64) (hs : xs.size < 2 ^ 64) (hlen : xs.size = ys.size)
    {a b : Nat → Rat} {B : Rat} (hB : 0 ≤ B)
    (hx : ∀ i (h : i < xs.size), xs[i].toRat? = some (a i) ∧ -B ≤ a i ∧ a i ≤ B)
    (hy : ∀ i (h : i < ys.size), ys[i].toRat? = some (b i) ∧ -B ≤ b i ∧ b i ≤ B)
    (hov : xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size < Ω64) :
    ∃ r q, dot xs ys = pure r ∧ r.toRat? = some q ∧
      -(xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size) ≤ q ∧
      q ≤ xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size ∧
      q - Zig.ratSum (fun i => a i * b i) xs.size ≤
        xs.size * (u64 * xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size + η64) +
          xs.size * (u64 * (B * B) + η64) ∧
      Zig.ratSum (fun i => a i * b i) xs.size - q ≤
        xs.size * (u64 * xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size + η64) +
          xs.size * (u64 * (B * B) + η64) := by
  have hu := Rat.le_of_lt (Zig.FloatFmt.unitRoundoff_pos .f64)
  have hη := Rat.le_of_lt (Zig.FloatFmt.underflowError_pos .f64)
  have hρ : (1 : Rat) ≤ 1 + u64 := by grind
  have hBB := Rat.mul_nonneg hB hB
  have hT : 0 ≤ B * B * (1 + u64) + η64 := by
    have := Rat.mul_nonneg hBB (show (0 : Rat) ≤ 1 + u64 by grind)
    grind
  have hc : B * B * (1 + u64) + η64 + η64 = B * B * (1 + u64) + 2 * η64 := by grind
  -- Every product is finite: `B² ≤ T ≤ n·c·ρⁿ < 2^1023` once there is a term.
  have hterm : ∀ k < xs.size, B * B < Ω64 ∧ ∃ v, (dotTerm xs ys k).toRat? = some v ∧
      v - a k * b k ≤ u64 * (B * B) + η64 ∧ a k * b k - v ≤ u64 * (B * B) + η64 ∧
      -(B * B * (1 + u64) + η64) ≤ v ∧ v ≤ B * B * (1 + u64) + η64 := by
    intro k hk
    have hmono := Zig.uniformBound_mono (Nat.zero_lt_of_lt hk) hρ hη hT
    rw [hc] at hmono
    have hBu := Rat.mul_nonneg hBB hu
    have hov' : B * B < Ω64 := by grind
    exact ⟨hov', dotTerm_error xs ys hk (hlen ▸ hk) (hx k hk) (hy k (hlen ▸ hk)) hov'⟩
  let v : Nat → Rat := fun k => ((dotTerm xs ys k).toRat?).getD 0
  have hv : ∀ k < xs.size, (dotTerm xs ys k).toRat? = some (v k) ∧
      v k - a k * b k ≤ u64 * (B * B) + η64 ∧ a k * b k - v k ≤ u64 * (B * B) + η64 ∧
      -(B * B * (1 + u64) + η64) ≤ v k ∧ v k ≤ B * B * (1 + u64) + η64 := by
    intro k hk
    obtain ⟨_, w, hw, h⟩ := hterm k hk
    simp only [v, hw, Option.getD_some]
    exact ⟨by trivial, h⟩
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := Zig.sumLeft_error_uniform (fmt := .f64)
    (init := Zig.Float.ofBits (0 : BitVec 64)) (t := dotTerm xs ys) (v := v) dot_init_toRat hT
    (fun k hk => ⟨(hv k hk).1, (hv k hk).2.2.2⟩) (by rw [hc]; exact hov)
  obtain ⟨d1, d2⟩ := Zig.ratSum_sub_le (n := xs.size) (v := v) (w := fun i => a i * b i)
    (fun k hk => ⟨(hv k hk).2.1, (hv k hk).2.2.1⟩)
  rw [hc] at h1 h2 h3 h4
  exact ⟨_, r, dot_eq_sumLeft xs ys hs hlen, hr, h1, h2, by grind, by grind⟩

/-- **NaN condition of `dot`.** One NaN element in either slice makes the result NaN. -/
theorem dot_isNaN (xs ys : Array Zig.F64) (hs : xs.size < 2 ^ 64) (hlen : xs.size = ys.size)
    {i : Nat} (hi : i < xs.size) (h : xs[i].isNaN = true ∨ (ys[i]'(hlen ▸ hi)).isNaN = true) :
    ∃ r, dot xs ys = pure r ∧ r.isNaN = true := by
  refine ⟨_, dot_eq_sumLeft xs ys hs hlen, Zig.sumLeft_isNaN _ _ hi ?_⟩
  simp only [dotTerm, getElem!_pos xs i hi, getElem!_pos ys i (hlen ▸ hi)]
  rcases h with h | h
  · exact Zig.mul_isNaN_left h _
  · exact Zig.mul_isNaN_right _ h

/-- **Stable sign of `dot`.** Under `dot_error`'s hypotheses, when the exact dot product
exceeds the error bound, the computed result compares greater than `+0`. -/
theorem dot_pos_of_gap (xs ys : Array Zig.F64) (hs : xs.size < 2 ^ 64) (hlen : xs.size = ys.size)
    {a b : Nat → Rat} {B : Rat} (hB : 0 ≤ B)
    (hx : ∀ i (h : i < xs.size), xs[i].toRat? = some (a i) ∧ -B ≤ a i ∧ a i ≤ B)
    (hy : ∀ i (h : i < ys.size), ys[i].toRat? = some (b i) ∧ -B ≤ b i ∧ b i ≤ B)
    (hov : xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size < Ω64)
    (hgap : xs.size * (u64 * xs.size * (B * B * (1 + u64) + 2 * η64) * (1 + u64) ^ xs.size + η64) +
          xs.size * (u64 * (B * B) + η64) < Zig.ratSum (fun i => a i * b i) xs.size) :
    ∃ r, dot xs ys = pure r ∧ Zig.Float.lt (Zig.Float.ofBits (0 : BitVec 64) : Zig.F64) r = true := by
  obtain ⟨r, q, hdot, hq, -, -, -, herr⟩ := dot_error xs ys hs hlen hB hx hy hov
  exact ⟨r, hdot, Zig.lt_of_error (w := 0) hq dot_init_toRat herr (by grind)⟩

/-! ## Non-vacuity witnesses -/

nonvacuity_witness dot_eq_sumLeft :=
  ⟨#[Zig.Float.ofBits 0], #[Zig.Float.ofBits 0], by decide, rfl, trivial⟩
