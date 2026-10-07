import ZigLean.Float.RoundTrip

/-!
# Rounding error, finite closure and accumulated error

Practical bounds on top of the exact rounding model (`docs/floats.md` §Semantics and
§Numerical bounds). Values are the exact `Rat`s of `Float.toRat?`; a bound `-A ≤ q ≤ A`
is written as two inequalities.

* `roundRat_error`: one rounding of an exact value `q` with `|q| ≤ A < 2^emax` gives a finite
  value `r` with `|r - q| ≤ u·A + η` (`u = 2^-prec`, `η = 2^(emin - prec)`).
* `add_error`/`mul_error`: the same for one `+`/`*` of finite operands: finite closure under
  an explicit magnitude bound, plus the rounding error.
* `sumLeft_error`: the accumulated error of the left fold `((init + t₀) + t₁) + …`, from a
  magnitude bound `M` and an error bound `E` that the caller supplies per step.
  `sumLeft_error_uniform` instantiates them in closed form for a zero start and a uniform
  term bound. The proof follows the fold step by step; it never reassociates a float sum.
* `sumLeft_isNaN`: one NaN term makes the whole fold NaN.
* `lt_of_error`/`gt_of_error`: a comparison against a computed value is decided by the
  exact value whenever the exact value clears the threshold by more than the error bound.
-/

namespace Zig

namespace FloatFmt

/-- Unit roundoff `u = 2^-prec`. -/
def unitRoundoff (fmt : FloatFmt) : Rat := (2 : Rat) ^ (-(fmt.prec : Int))

/-- Absolute underflow error `η = 2^(emin - prec)`: half the subnormal spacing. -/
def underflowError (fmt : FloatFmt) : Rat := (2 : Rat) ^ (fmt.emin - fmt.prec)

/-- Overflow threshold `2^emax`. Every exact value of smaller magnitude rounds to a finite
value. It is conservative: values up to `(2 - 2^-prec)·2^emax` also stay finite. -/
def overflowBound (fmt : FloatFmt) : Rat := (2 : Rat) ^ fmt.emax

theorem unitRoundoff_pos (fmt : FloatFmt) : 0 < fmt.unitRoundoff := Rat.zpow_pos (by decide)

theorem underflowError_pos (fmt : FloatFmt) : 0 < fmt.underflowError := Rat.zpow_pos (by decide)

/-- `f64`: `u = 2^-53`, `η = 2^-1075`, overflow bound `2^1023`. -/
theorem f64_constants :
    FloatFmt.f64.unitRoundoff = (2 : Rat) ^ (-53 : Int) ∧
    FloatFmt.f64.underflowError = (2 : Rat) ^ (-1075 : Int) ∧
    FloatFmt.f64.overflowBound = (2 : Rat) ^ (1023 : Int) := ⟨rfl, rfl, rfl⟩

end FloatFmt

/-! ## Powers of two -/

private theorem two_zpow_pos (e : Int) : 0 < (2 : Rat) ^ e := Rat.zpow_pos (by decide)

/-- `2 ^ e⁺ = 2 ^ e * 2 ^ e⁻`: the split `finiteToRat` and `roundMant` use. -/
private theorem two_pow_toNat (e : Int) :
    (2 : Rat) ^ e.toNat = (2 : Rat) ^ e * (2 : Rat) ^ (-e).toNat := by
  rw [← Rat.zpow_natCast, ← Rat.zpow_natCast, ← Rat.zpow_add (by decide)]
  congr 1
  omega

private theorem one_le_two_pow (k : Nat) : (1 : Rat) ≤ (2 : Rat) ^ k := by
  have h : ((1 : Nat) : Rat) ≤ ((2 ^ k : Nat) : Rat) := Rat.natCast_le_natCast.mpr Nat.one_le_two_pow
  simpa using h

private theorem two_zpow_le {a b : Int} (h : a ≤ b) : (2 : Rat) ^ a ≤ (2 : Rat) ^ b := by
  have hb : b = a + ((b - a).toNat : Nat) := by omega
  rw [hb, Rat.zpow_add (by decide), Rat.zpow_natCast]
  have h1 := one_le_two_pow (b - a).toNat
  have h2 := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (two_zpow_pos a))
  grind

/-- A finite magnitude `m * 2^e`, with an integer power. -/
theorem finiteToRat_false_eq_zpow (m : Nat) (e : Int) :
    finiteToRat false m e = (m : Rat) * (2 : Rat) ^ e := by
  unfold finiteToRat
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rw [← Rat.zpow_natCast]
    congr 2
    omega
  · have he : e = -(((-e).toNat : Nat) : Int) := by omega
    conv => rhs; rw [he]
    rw [Rat.zpow_neg, Rat.zpow_natCast, Rat.div_def]

private theorem finiteToRat_true_eq (m : Nat) (e : Int) :
    finiteToRat true m e = -finiteToRat false m e := by
  unfold finiteToRat
  simp

/-- The shift-form bound `d * 2^L ≤ n` (`ilog2_low`) as a `Rat` bound. -/
private theorem two_zpow_mul_le {n d : Nat} {L : Int}
    (h : d * 2 ^ L.toNat ≤ n * 2 ^ (-L).toNat) : (2 : Rat) ^ L * d ≤ n := by
  have hc : ((d * 2 ^ L.toNat : Nat) : Rat) ≤ ((n * 2 ^ (-L).toNat : Nat) : Rat) :=
    Rat.natCast_le_natCast.mpr h
  push_cast at hc
  rw [two_pow_toNat L] at hc
  have hP : (0 : Rat) < (2 : Rat) ^ (-L).toNat := Rat.pow_pos (by decide)
  apply Rat.le_of_mul_le_mul_right _ hP
  grind

/-! ## One rounding -/

/-- Round half to even is within half a unit of the quotient: `|M * D - N| ≤ D / 2`. -/
theorem roundQuot_half (N D : Nat) (hD : 0 < D) :
    2 * (roundQuot N D * D - N) ≤ (D : Int) ∧ 2 * ((N : Int) - roundQuot N D * D) ≤ D := by
  have h := Nat.div_add_mod N D
  have hr := Nat.mod_lt N hD
  unfold roundQuot
  simp only []
  generalize N / D = q at *
  generalize N % D = r at *
  have hc : ((D * q : Nat) : Int) = (q : Int) * D := by push_cast; exact Int.mul_comm _ _
  have hN : (N : Int) = (q : Int) * D + r := by omega
  -- `try split` per level, as in `roundQuot_le`: the proof also holds for `scripts/mutate.sh`
  -- (d), which removes the tie-to-even branch.
  split <;> (try split) <;> (try split) <;> (try rw [Int.add_mul]) <;> omega

/-- A nonnegative rational times its denominator is its numerator. -/
private theorem mul_den_eq_num {x : Rat} (hx : 0 ≤ x) : x * x.den = (x.num.toNat : Nat) := by
  have h := Rat.mkRat_self x
  rw [Rat.mkRat_eq_div] at h
  have hd : (x.den : Rat) ≠ 0 := by
    have : (0 : Rat) < x.den := Rat.natCast_pos.mpr x.den_pos
    exact fun h0 => by rw [h0] at this; exact Rat.lt_irrefl this
  have hn : ((x.num.toNat : Nat) : Rat) = (x.num : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)]
  rw [hn]
  conv => lhs; rw [← h]
  grind

/-- The rounded magnitude `roundMant * 2^roundExp` of `x = n / d` is within `2^roundExp / 2`. -/
private theorem roundMant_half (fmt : FloatFmt) {n d : Nat} (hd : 0 < d) {x : Rat}
    (hx : x * d = n) :
    2 * ((roundMant fmt n d).toNat * (2 : Rat) ^ (roundExp fmt n d) - x)
        ≤ (2 : Rat) ^ (roundExp fmt n d) ∧
      2 * (x - (roundMant fmt n d).toNat * (2 : Rat) ^ (roundExp fmt n d))
        ≤ (2 : Rat) ^ (roundExp fmt n d) := by
  unfold roundMant
  simp only []
  generalize roundExp fmt n d = E
  have hD : 0 < d * 2 ^ E.toNat := Nat.mul_pos hd (Nat.two_pow_pos _)
  have hq := roundQuot_half (n * 2 ^ (-E).toNat) (d * 2 ^ E.toNat) hD
  have hM0 := Int.le_trans (Int.natCast_nonneg _)
    (roundQuot_bounds (n * 2 ^ (-E).toNat) (d * 2 ^ E.toNat)).1
  generalize roundQuot (n * 2 ^ (-E).toNat) (d * 2 ^ E.toNat) = M at hq hM0
  obtain ⟨Mn, rfl⟩ : ∃ Mn : Nat, M = Mn := ⟨M.toNat, (Int.toNat_of_nonneg hM0).symm⟩
  rw [Int.toNat_natCast]
  have h1 := Rat.intCast_le_intCast.mpr hq.1
  have h2 := Rat.intCast_le_intCast.mpr hq.2
  push_cast at h1 h2
  rw [two_pow_toNat E] at h1 h2
  have hP : (0 : Rat) < (2 : Rat) ^ (-E).toNat := Rat.pow_pos (by decide)
  have hd' : (0 : Rat) < d := Rat.natCast_pos.mpr hd
  have hdP := Rat.mul_pos hd' hP
  have hxP : x * d * (2 : Rat) ^ (-E).toNat = n * (2 : Rat) ^ (-E).toNat := by rw [hx]
  constructor
  · apply Rat.le_of_mul_le_mul_right _ hdP
    grind
  · apply Rat.le_of_mul_le_mul_right _ hdP
    grind

/-- The unit in the last place at `roundExp` is at most `2·(x·u + η)` for `x = n / d`. -/
private theorem ulp_le (fmt : FloatFmt) {n d : Nat} (hn : 0 < n) (hd : 0 < d) {x : Rat}
    (hx : x * d = n) :
    (2 : Rat) ^ (roundExp fmt n d) ≤ 2 * (x * fmt.unitRoundoff + fmt.underflowError) := by
  have hd' : (0 : Rat) < d := Rat.natCast_pos.mpr hd
  have hx0 : 0 ≤ x := by
    apply Rat.not_lt.mp
    intro hneg
    have h1 := (Rat.mul_neg_iff_of_pos_right hd').mpr hneg
    rw [hx] at h1
    exact Rat.not_lt.mpr Rat.natCast_nonneg h1
  have hu := FloatFmt.unitRoundoff_pos fmt
  have hη := FloatFmt.underflowError_pos fmt
  have hxu := Rat.mul_nonneg hx0 (Rat.le_of_lt hu)
  have hpf : ((fmt.prec : Int) - 1) = fmt.fracBits := by simp only [FloatFmt.prec]; omega
  have hcase : roundExp fmt n d = ilog2 n d - ((fmt.prec : Int) - 1) ∨
      roundExp fmt n d = fmt.emin - ((fmt.prec : Int) - 1) := by
    unfold roundExp; omega
  rcases hcase with he | he
  · -- Normal: `2^E = 2 · 2^L · u` and `2^L ≤ x`.
    have hL : (2 : Rat) ^ (ilog2 n d) ≤ x := by
      have h := two_zpow_mul_le (ilog2_low hn hd)
      rw [← hx] at h
      exact Rat.le_of_mul_le_mul_right h hd'
    have hsplit : roundExp fmt n d = (ilog2 n d + -(fmt.prec : Int)) + 1 := by omega
    rw [hsplit, Rat.zpow_add_one (by decide), Rat.zpow_add (by decide)]
    have h2 := Rat.mul_le_mul_of_nonneg_right hL (Rat.le_of_lt hu)
    unfold FloatFmt.unitRoundoff at h2 hxu ⊢
    grind
  · -- Subnormal: `2^E = 2η`.
    have hsplit : roundExp fmt n d = (fmt.emin - (fmt.prec : Int)) + 1 := by omega
    rw [hsplit, Rat.zpow_add_one (by decide)]
    unfold FloatFmt.underflowError at hη ⊢
    grind

/-- `finalizeRounded` does not overflow below the exponent `emax - prec`. -/
private theorem finalizeRounded_isSome (fmt : FloatFmt) (s : Bool) {M e0 : Int}
    (hM : M ≤ 2 ^ fmt.prec) (he_lo : fmt.emin - fmt.fracBits ≤ e0)
    (hnorm : 2 ^ fmt.fracBits ≤ M ∨ e0 = fmt.emin - fmt.fracBits)
    (hov : e0 + fmt.prec ≤ fmt.emax) :
    ∃ r, (Float.finalizeRounded fmt s M e0).toRat? = some r := by
  have hcast : (((2 ^ fmt.prec : Nat)) : Int) = (2 : Int) ^ fmt.prec := by push_cast; rfl
  have hcastf : (((2 ^ fmt.fracBits : Nat)) : Int) = (2 : Int) ^ fmt.fracBits := by
    push_cast; rfl
  have hp : (2 : Nat) ^ fmt.prec = 2 ^ fmt.fracBits * 2 ^ 1 := by rw [← Nat.pow_add]; rfl
  have hpf : fmt.prec - 1 = fmt.fracBits := by simp only [FloatFmt.prec]; omega
  unfold Float.finalizeRounded
  by_cases hc : M = (2 : Int) ^ fmt.prec
  · rw [ite_eq_left hc]
    simp only []
    rw [ite_eq_right (by omega), hpf]
    have hcl := classify_encodeFinite fmt s (m := 2 ^ fmt.fracBits) (e := e0 + 1)
      (Nat.two_pow_pos _) (by rw [hp]; have := Nat.two_pow_pos fmt.fracBits; omega)
      (by omega) (by omega) (Or.inl (Nat.le_refl _))
    exact ⟨_, by unfold Float.toRat?; rw [hcl]⟩
  · rw [ite_eq_right hc]
    simp only []
    rw [ite_eq_right (by omega)]
    by_cases hM0' : M.toNat = 0
    · rw [hM0']
      unfold Float.encodeFinite
      rw [ite_eq_left rfl]
      exact ⟨_, by unfold Float.toRat?; rw [classify_zero]⟩
    · have hcl := classify_encodeFinite fmt s (m := M.toNat) (e := e0)
        (by omega) (by rw [← hcast] at hM hc; omega) he_lo (by omega)
        (by rw [← hcastf] at hnorm; omega)
      exact ⟨_, by unfold Float.toRat?; rw [hcl]⟩

/-- **Finite closure of rounding.** An exact value of magnitude below `2^emax` rounds to a
finite value, with either sign flag. -/
theorem roundRat_isSome (fmt : FloatFmt) (s : Bool) {q : Rat}
    (hov : q.abs < fmt.overflowBound) : ∃ r, (Float.roundRat fmt s q).toRat? = some r := by
  by_cases hq : q = 0
  · subst hq
    rw [roundRat_zero]
    exact ⟨_, by unfold Float.toRat?; rw [classify_zero]⟩
  have habs : q.abs ≠ 0 := fun h => hq (Rat.abs_eq_zero_iff.mp h)
  have hnn : 0 ≤ q.abs.num := Rat.num_nonneg.mpr Rat.abs_nonneg
  have hn : 0 < q.abs.num.toNat := by
    have : q.abs.num ≠ 0 := fun h0 => habs (Rat.num_eq_zero.mp h0)
    omega
  have hd := q.abs.den_pos
  have hx := mul_den_eq_num (Rat.abs_nonneg (x := q))
  rw [roundRat_eq_finalize fmt s hq]
  generalize q.abs.num.toNat = n at hn hx ⊢
  generalize q.abs.den = d at hd hx ⊢
  have hM := roundMant_le fmt hn hd
  have hpf : ((fmt.prec : Int) - 1) = fmt.fracBits := by simp only [FloatFmt.prec]; omega
  -- `2^L ≤ |q| < 2^emax` puts `L` below `emax`.
  have hL : ilog2 n d + 1 ≤ fmt.emax := by
    apply Int.not_lt.mp
    intro hlt
    have h1 := two_zpow_mul_le (ilog2_low hn hd)
    rw [← hx] at h1
    have h2 := Rat.le_of_mul_le_mul_right h1 (Rat.natCast_pos.mpr hd)
    have h3 := two_zpow_le (show fmt.emax ≤ ilog2 n d by omega)
    unfold FloatFmt.overflowBound at hov
    grind
  have hemin : fmt.emin + 1 ≤ fmt.emax := by cases fmt <;> decide
  apply finalizeRounded_isSome fmt s hM (roundExp_lo fmt n d) (roundMant_norm fmt hn hd)
  unfold roundExp
  omega

/-- **One rounding.** Rounding an exact value `q` with `|q| ≤ A < 2^emax`, with the sign flag
of `q` (any flag when `q = 0`), gives a finite value within `u·A + η` of `q`. -/
theorem roundRat_error (fmt : FloatFmt) {neg : Bool} {q A : Rat}
    (hsign : q ≠ 0 → neg = decide (q < 0)) (hlo : -A ≤ q) (hhi : q ≤ A)
    (hov : A < fmt.overflowBound) :
    ∃ r, (Float.roundRat fmt neg q).toRat? = some r ∧
      r - q ≤ fmt.unitRoundoff * A + fmt.underflowError ∧
      q - r ≤ fmt.unitRoundoff * A + fmt.underflowError := by
  have hu := FloatFmt.unitRoundoff_pos fmt
  have hη := FloatFmt.underflowError_pos fmt
  have hA0 : 0 ≤ A := by grind
  have huA := Rat.mul_nonneg (Rat.le_of_lt hu) hA0
  by_cases hq : q = 0
  · subst hq
    rw [roundRat_zero]
    refine ⟨0, by simp [Float.toRat?, classify_zero, finiteToRat_zero], ?_, ?_⟩ <;> grind
  have hsgn := hsign hq
  have hcases : (0 < q ∧ q.abs = q) ∨ (q < 0 ∧ q.abs = -q) := by
    rcases Rat.le_total (a := 0) (b := q) with h | h
    · exact Or.inl ⟨Rat.lt_of_le_of_ne h (Ne.symm hq), Rat.abs_of_nonneg h⟩
    · exact Or.inr ⟨Rat.lt_of_le_of_ne h hq, Rat.abs_of_nonpos h⟩
  have hxA : q.abs ≤ A := by rcases hcases with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> grind
  obtain ⟨r, hr⟩ := roundRat_isSome fmt neg (q := q) (by grind)
  refine ⟨r, hr, ?_⟩
  have hval := roundRat_toRat_value fmt neg hq hr
  have habs : q.abs ≠ 0 := fun h => hq (Rat.abs_eq_zero_iff.mp h)
  have hnn : 0 ≤ q.abs.num := Rat.num_nonneg.mpr Rat.abs_nonneg
  have hn : 0 < q.abs.num.toNat := by
    have : q.abs.num ≠ 0 := fun h0 => habs (Rat.num_eq_zero.mp h0)
    omega
  have hx := mul_den_eq_num (Rat.abs_nonneg (x := q))
  have hhalf := roundMant_half fmt q.abs.den_pos hx
  have hulp := ulp_le fmt hn q.abs.den_pos hx
  have hmono := Rat.mul_le_mul_of_nonneg_right hxA (Rat.le_of_lt hu)
  rcases hcases with ⟨hpos, habsq⟩ | ⟨hneg, habsq⟩
  · have : neg = false := by
      rw [hsgn]; exact decide_eq_false (Rat.not_lt.mpr (Rat.le_of_lt hpos))
    subst this
    rw [finiteToRat_false_eq_zpow] at hval
    rw [habsq] at hhalf hulp hmono
    constructor <;> grind
  · have : neg = true := by rw [hsgn]; exact decide_eq_true hneg
    subst this
    rw [finiteToRat_true_eq, finiteToRat_false_eq_zpow] at hval
    rw [habsq] at hhalf hulp hmono
    constructor <;> grind

/-! ## `+` and `*` -/

/-- **Finite closure and error of `+`.** Finite operands whose exact sum has magnitude at most
`A < 2^emax` add to a finite value within `u·A + η` of the exact sum. -/
theorem add_error {fmt : FloatFmt} {x y : Float fmt} {a b A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hlo : -A ≤ a + b) (hhi : a + b ≤ A)
    (hov : A < fmt.overflowBound) :
    ∃ r, (Float.add x y).toRat? = some r ∧
      r - (a + b) ≤ fmt.unitRoundoff * A + fmt.underflowError ∧
      (a + b) - r ≤ fmt.unitRoundoff * A + fmt.underflowError := by
  obtain ⟨sa, ma, ea, hxc, rfl⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, rfl⟩ := exists_finite_of_toRat? hy
  unfold Float.add
  rw [hxc, hyc]
  exact roundRat_error fmt (fun hq => by simp only [hq, ↓reduceIte]) hlo hhi hov

private theorem finiteToRat_false_pos {m : Nat} (hm : m ≠ 0) (e : Int) :
    0 < finiteToRat false m e :=
  Rat.lt_of_le_of_ne (finiteToRat_nonneg m e) (Ne.symm (finiteToRat_ne_zero false hm e))

/-- **Finite closure and error of `*`.** Finite operands whose exact product has magnitude at
most `A < 2^emax` multiply to a finite value within `u·A + η` of the exact product. -/
theorem mul_error {fmt : FloatFmt} {x y : Float fmt} {a b A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hlo : -A ≤ a * b) (hhi : a * b ≤ A)
    (hov : A < fmt.overflowBound) :
    ∃ r, (Float.mul x y).toRat? = some r ∧
      r - a * b ≤ fmt.unitRoundoff * A + fmt.underflowError ∧
      a * b - r ≤ fmt.unitRoundoff * A + fmt.underflowError := by
  obtain ⟨sa, ma, ea, hxc, rfl⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, rfl⟩ := exists_finite_of_toRat? hy
  rw [mul_of_finite hxc hyc]
  refine roundRat_error fmt (fun hq => ?_) hlo hhi hov
  have hma : ma ≠ 0 := fun h => hq (by rw [h, finiteToRat_zero, Rat.zero_mul])
  have hmb : mb ≠ 0 := fun h => hq (by rw [h, finiteToRat_zero, Rat.mul_zero])
  have hpa := finiteToRat_false_pos hma ea
  have hpb := finiteToRat_false_pos hmb eb
  have hpp := Rat.mul_pos hpa hpb
  by_cases hlt : finiteToRat sa ma ea * finiteToRat sb mb eb < 0
  · rw [decide_eq_true hlt]
    cases sa <;> cases sb <;> (try simp only [finiteToRat_true_eq] at hlt) <;>
      first | rfl | (exfalso; grind)
  · rw [decide_eq_false hlt]
    cases sa <;> cases sb <;> (try simp only [finiteToRat_true_eq] at hlt) <;>
      first | rfl | (exfalso; grind)

/-! ## NaN propagation -/

theorem add_isNaN_left {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    (Float.add x y).isNaN = true := by
  unfold Float.add
  rw [(isNaN_iff x).mp h]
  exact isNaN_nan

theorem add_isNaN_right {fmt : FloatFmt} (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    (Float.add x y).isNaN = true := by
  unfold Float.add
  rw [(isNaN_iff y).mp h]
  cases x.classify <;> exact isNaN_nan

theorem mul_isNaN_left {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    (Float.mul x y).isNaN = true := by
  unfold Float.mul
  rw [(isNaN_iff x).mp h]
  exact isNaN_nan

theorem mul_isNaN_right {fmt : FloatFmt} (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    (Float.mul x y).isNaN = true := by
  unfold Float.mul
  rw [(isNaN_iff y).mp h]
  cases x.classify <;> exact isNaN_nan

/-! ## Left-fold sums -/

/-- The left fold of `+` over the terms `t 0, …, t (n - 1)` from `init`:
`((init + t 0) + t 1) + …`, the order a sequential accumulation loop adds in. -/
def Float.sumLeft {fmt : FloatFmt} (init : Float fmt) (t : Nat → Float fmt) : Nat → Float fmt
  | 0 => init
  | k + 1 => Float.add (Float.sumLeft init t k) (t k)

/-- The exact sum `v 0 + … + v (n - 1)`. -/
def ratSum (v : Nat → Rat) : Nat → Rat
  | 0 => 0
  | k + 1 => ratSum v k + v k

/-- One NaN term makes the left-fold sum NaN: `+` propagates NaN from either side. -/
theorem sumLeft_isNaN {fmt : FloatFmt} (init : Float fmt) (t : Nat → Float fmt) {i n : Nat}
    (hi : i < n) (h : (t i).isNaN = true) : (Float.sumLeft init t n).isNaN = true := by
  induction n with
  | zero => omega
  | succ k ih =>
    unfold Float.sumLeft
    by_cases hk : i < k
    · exact add_isNaN_left (ih hk) _
    · have : i = k := by omega
      subst this
      exact add_isNaN_right _ h

/-- **Accumulated error of a left-fold sum.** `M k` bounds the magnitude of the `k`-th
partial sum and `E k` its distance from the exact partial sum; each step must absorb one
rounding of a sum of magnitude at most `M k + T k`. Then every intermediate sum is finite,
and the result is within `E n` of `s0 + ∑ v`. -/
theorem sumLeft_error {fmt : FloatFmt} {init : Float fmt} {t : Nat → Float fmt} {s0 : Rat}
    {v T : Nat → Rat} (M E : Nat → Rat) {n : Nat}
    (hinit : init.toRat? = some s0) (hM0 : -M 0 ≤ s0 ∧ s0 ≤ M 0) (hE0 : 0 ≤ E 0)
    (hterm : ∀ k < n, (t k).toRat? = some (v k) ∧ -T k ≤ v k ∧ v k ≤ T k)
    (hM : ∀ k < n, (M k + T k) * (1 + fmt.unitRoundoff) + fmt.underflowError ≤ M (k + 1))
    (hE : ∀ k < n, E k + (fmt.unitRoundoff * (M k + T k) + fmt.underflowError) ≤ E (k + 1))
    (hov : ∀ k < n, M k + T k < fmt.overflowBound) :
    ∃ r, (Float.sumLeft init t n).toRat? = some r ∧ -M n ≤ r ∧ r ≤ M n ∧
      r - (s0 + ratSum v n) ≤ E n ∧ (s0 + ratSum v n) - r ≤ E n := by
  induction n with
  | zero =>
    refine ⟨s0, hinit, hM0.1, hM0.2, ?_, ?_⟩ <;> simp only [ratSum] <;> grind
  | succ k ih =>
    obtain ⟨r, hr, h1, h2, h3, h4⟩ := ih (fun j hj => hterm j (by omega))
      (fun j hj => hM j (by omega)) (fun j hj => hE j (by omega)) (fun j hj => hov j (by omega))
    obtain ⟨hv, hvlo, hvhi⟩ := hterm k (by omega)
    obtain ⟨r', hr', e1, e2⟩ := add_error hr hv (A := M k + T k) (by grind) (by grind)
      (hov k (by omega))
    have hMk := hM k (by omega)
    have hEk := hE k (by omega)
    refine ⟨r', hr', ?_, ?_, ?_, ?_⟩ <;> (try simp only [ratSum]) <;> grind

private theorem one_le_pow {ρ : Rat} (hρ : 1 ≤ ρ) (k : Nat) : 1 ≤ ρ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rat.pow_succ]
    have := Rat.mul_le_mul_of_nonneg_left hρ (Rat.le_trans (by decide) ih)
    grind

private theorem pow_le_pow {ρ : Rat} (hρ : 1 ≤ ρ) {k n : Nat} (h : k ≤ n) : ρ ^ k ≤ ρ ^ n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]; exact Rat.le_refl
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [Rat.pow_succ]
      have h1 := ih (by omega)
      have h2 := Rat.mul_le_mul_of_nonneg_left hρ (Rat.le_trans (by decide) (one_le_pow hρ n))
      grind
    · rw [h]; exact Rat.le_refl

/-- The magnitude step of `sumLeft_error_uniform` (`P = ρ^k`). -/
private theorem uniform_mag_step {u η T P : Rat} (k : Nat) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hT : 0 ≤ T) (hP : 1 ≤ P) :
    ((k : Rat) * (T + η) * P + T) * (1 + u) + η ≤ ((k + 1 : Nat) : Rat) * (T + η) * (P * (1 + u)) := by
  have h1 : 0 ≤ (T + η) * (P - 1) := Rat.mul_nonneg (by grind) (by grind)
  have h2 : 0 ≤ (T + η) * (P - 1) * u := Rat.mul_nonneg h1 hu
  have h3 : 0 ≤ η * u := Rat.mul_nonneg hη hu
  push_cast
  grind

/-- The error step of `sumLeft_error_uniform` (`P = ρ^k`). -/
private theorem uniform_err_step {u η T P : Rat} (k : Nat) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hT : 0 ≤ T) (hP : 1 ≤ P) :
    (k : Rat) * (u * k * (T + η) * P + η) + (u * ((k : Rat) * (T + η) * P + T) + η) ≤
      ((k + 1 : Nat) : Rat) * (u * ((k + 1 : Nat) : Rat) * (T + η) * (P * (1 + u)) + η) := by
  have hk : (0 : Rat) ≤ k := Rat.natCast_nonneg
  have hc : 0 ≤ T + η := by grind
  have h1 : 0 ≤ u * (T + η) * (P - 1) := Rat.mul_nonneg (Rat.mul_nonneg hu hc) (by grind)
  have h2 : 0 ≤ u * η := Rat.mul_nonneg hu hη
  have h3 : 0 ≤ u * (T + η) * P * k := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hu hc)
    (by grind)) hk
  have h4 : 0 ≤ u * u * (T + η) * P * ((k + 1) * (k + 1)) :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hu hu) hc) (by grind))
      (Rat.mul_nonneg (by grind) (by grind))
  push_cast
  grind

/-- The closed-form magnitude bound of `sumLeft_error_uniform` grows with the step: one more
term of magnitude `T` after step `k < n` stays below the bound at `n`. -/
theorem uniformBound_mono {ρ T η : Rat} {k n : Nat} (hk : k < n) (hρ : 1 ≤ ρ) (hη : 0 ≤ η)
    (hT : 0 ≤ T) : (k : Rat) * (T + η) * ρ ^ k + T ≤ n * (T + η) * ρ ^ n := by
  have hc : 0 ≤ T + η := by grind
  have hP := one_le_pow hρ k
  have hPn := pow_le_pow hρ (Nat.le_of_lt hk)
  have hkn : ((k + 1 : Nat) : Rat) ≤ n := Rat.natCast_le_natCast.mpr hk
  have h1 : T ≤ (T + η) * ρ ^ k := by
    have := Rat.mul_le_mul_of_nonneg_left hP hc
    grind
  have h2 := Rat.mul_le_mul_of_nonneg_right hkn (Rat.mul_nonneg hc (Rat.le_trans (by decide) hP))
  have h3 := Rat.mul_le_mul_of_nonneg_left hPn (Rat.mul_nonneg (Rat.natCast_nonneg (a := n)) hc)
  push_cast at h2
  grind

/-- **Accumulated error, closed form.** A left-fold sum from a zero of `n` finite terms, each
of magnitude at most `T`: with `c = T + η` and `ρ = 1 + u`, every intermediate sum is finite
when `n·c·ρⁿ < 2^emax`, the result has magnitude at most `n·c·ρⁿ`, and it is within
`n·(u·n·c·ρⁿ + η)` of the exact sum. -/
theorem sumLeft_error_uniform {fmt : FloatFmt} {init : Float fmt} {t : Nat → Float fmt}
    {v : Nat → Rat} {T : Rat} {n : Nat} (hinit : init.toRat? = some 0) (hT : 0 ≤ T)
    (hterm : ∀ k < n, (t k).toRat? = some (v k) ∧ -T ≤ v k ∧ v k ≤ T)
    (hov : n * (T + fmt.underflowError) * (1 + fmt.unitRoundoff) ^ n < fmt.overflowBound) :
    ∃ r, (Float.sumLeft init t n).toRat? = some r ∧
      -(n * (T + fmt.underflowError) * (1 + fmt.unitRoundoff) ^ n) ≤ r ∧
      r ≤ n * (T + fmt.underflowError) * (1 + fmt.unitRoundoff) ^ n ∧
      r - ratSum v n ≤ n * (fmt.unitRoundoff * n * (T + fmt.underflowError) *
        (1 + fmt.unitRoundoff) ^ n + fmt.underflowError) ∧
      ratSum v n - r ≤ n * (fmt.unitRoundoff * n * (T + fmt.underflowError) *
        (1 + fmt.unitRoundoff) ^ n + fmt.underflowError) := by
  have hu := Rat.le_of_lt (FloatFmt.unitRoundoff_pos fmt)
  have hη := Rat.le_of_lt (FloatFmt.underflowError_pos fmt)
  have hρ : (1 : Rat) ≤ 1 + fmt.unitRoundoff := by grind
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := sumLeft_error (fmt := fmt) (init := init) (t := t) (s0 := 0)
    (v := v) (T := fun _ => T) (n := n)
    (fun k => k * (T + fmt.underflowError) * (1 + fmt.unitRoundoff) ^ k)
    (fun k => k * (fmt.unitRoundoff * k * (T + fmt.underflowError) *
      (1 + fmt.unitRoundoff) ^ k + fmt.underflowError)) hinit (by simp) (by simp) hterm
    (fun k _ => by
      simp only [Rat.pow_succ]
      exact uniform_mag_step k hu hη hT (one_le_pow hρ k))
    (fun k _ => by
      simp only [Rat.pow_succ]
      exact uniform_err_step k hu hη hT (one_le_pow hρ k))
    (fun k hk => by have := uniformBound_mono hk hρ hη hT; grind)
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩ <;> grind

/-- Termwise bounds add up: `|∑ v - ∑ w| ≤ n·δ` when every `|v k - w k| ≤ δ`. -/
theorem ratSum_sub_le {v w : Nat → Rat} {δ : Rat} {n : Nat}
    (h : ∀ k < n, v k - w k ≤ δ ∧ w k - v k ≤ δ) :
    ratSum v n - ratSum w n ≤ n * δ ∧ ratSum w n - ratSum v n ≤ n * δ := by
  induction n with
  | zero => simp only [ratSum]; constructor <;> grind
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨h3, h4⟩ := h k (by omega)
    simp only [ratSum]
    push_cast
    constructor <;> grind

/-! ## Comparisons -/

/-- **Stable comparison, from above.** A computed `y` within `e` below an exact `s` (`s - q ≤ e`)
compares greater than a threshold `z` whenever `s` clears `z`'s value by more than `e`. -/
theorem lt_of_error {fmt : FloatFmt} {y z : Float fmt} {q w s e : Rat}
    (hy : y.toRat? = some q) (hz : z.toRat? = some w) (herr : s - q ≤ e) (hgap : w + e < s) :
    Float.lt z y = true := by
  rw [lt_of_toRat hz hy]
  exact decide_eq_true (by grind)

/-- **Stable comparison, from below.** A computed `y` within `e` above an exact `s`
(`q - s ≤ e`) compares less than `z` whenever `s` stays below `z`'s value by more than `e`. -/
theorem gt_of_error {fmt : FloatFmt} {y z : Float fmt} {q w s e : Rat}
    (hy : y.toRat? = some q) (hz : z.toRat? = some w) (herr : q - s ≤ e) (hgap : s + e < w) :
    Float.lt y z = true := by
  rw [lt_of_toRat hy hz]
  exact decide_eq_true (by grind)

end Zig
