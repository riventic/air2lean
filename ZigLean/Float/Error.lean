import ZigLean.Float.RoundTrip
import ZigLean.Float.CompilerRt

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
value. It is conservative: magnitudes below `(2 - 2^-prec)·2^emax` also stay finite. -/
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

/-- A nonzero rational's magnitude has a positive numerator. -/
private theorem abs_num_toNat_pos {q : Rat} (hq : q ≠ 0) : 0 < q.abs.num.toNat := by
  have habs : q.abs ≠ 0 := fun h => hq (Rat.abs_eq_zero_iff.mp h)
  have hnn : 0 ≤ q.abs.num := Rat.num_nonneg.mpr Rat.abs_nonneg
  have : q.abs.num ≠ 0 := fun h0 => habs (Rat.num_eq_zero.mp h0)
  omega

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
  have hn := abs_num_toNat_pos hq
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
  have hn := abs_num_toNat_pos hq
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

/-! ## Products of bounded values -/

/-- `|a·b| ≤ A·B` for `|a| ≤ A` and `|b| ≤ B`. -/
theorem mul_abs_le {a b A B : Rat} (ha : -A ≤ a ∧ a ≤ A) (hb : -B ≤ b ∧ b ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  have h1 := Rat.mul_nonneg (show 0 ≤ A - a by grind) (show 0 ≤ B - b by grind)
  have h2 := Rat.mul_nonneg (show 0 ≤ A + a by grind) (show 0 ≤ B + b by grind)
  have h3 := Rat.mul_nonneg (show 0 ≤ A - a by grind) (show 0 ≤ B + b by grind)
  have h4 := Rat.mul_nonneg (show 0 ≤ A + a by grind) (show 0 ≤ B - b by grind)
  constructor <;> grind

/-- A perturbed product: `|a·b - a'·b'| ≤ A·δb + δa·B'` for `|a| ≤ A`, `|b'| ≤ B'`,
`|a - a'| ≤ δa` and `|b - b'| ≤ δb`. Propagates an earlier rounding error through `*`. -/
theorem mul_sub_mul_le {a b a' b' A B' δa δb : Rat} (ha : -A ≤ a ∧ a ≤ A)
    (hb' : -B' ≤ b' ∧ b' ≤ B') (hda : -δa ≤ a - a' ∧ a - a' ≤ δa)
    (hdb : -δb ≤ b - b' ∧ b - b' ≤ δb) :
    -(A * δb + δa * B') ≤ a * b - a' * b' ∧ a * b - a' * b' ≤ A * δb + δa * B' := by
  have e : a * b - a' * b' = a * (b - b') + (a - a') * b' := by grind
  obtain ⟨p1, p2⟩ := mul_abs_le ha hdb
  obtain ⟨q1, q2⟩ := mul_abs_le hda hb'
  rw [e]
  constructor <;> grind

/-! ## `-` -/

/-- Flipping bit `w - 1` leaves every bit field below it unchanged. -/
private theorem xor_top_field {v w R k : Nat} (h : R + k ≤ w - 1) :
    ((v ^^^ 2 ^ (w - 1)) >>> R) % 2 ^ k = (v >>> R) % 2 ^ k := by
  rw [Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow, Nat.shiftRight_eq_div_pow (2 ^ (w - 1)),
    Nat.pow_div (by omega) (by decide)]
  have : 2 ^ (w - 1 - R) % 2 ^ k = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
  rw [this, Nat.xor_zero]

private theorem neg_bits_toNat {fmt : FloatFmt} (x : Float fmt) :
    (Float.neg x).bits.toNat = x.bits.toNat ^^^ 2 ^ (fmt.width - 1) := by
  have hw : 1 ≤ fmt.width := by cases fmt <;> decide
  have hlt := x.bits.isLt
  have hp : (2 : Nat) ^ (fmt.width - 1) < 2 ^ fmt.width := Nat.pow_lt_pow_right (by decide) (by omega)
  unfold Float.neg
  rw [BitVec.toNat_ofNat, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hlt hp)

/-- `neg` is `pack` of the flipped sign bit and the unchanged exponent field and low bits. -/
theorem neg_eq_pack {fmt : FloatFmt} (x : Float fmt) :
    Float.neg x = Float.pack fmt (!x.bits.msb)
      ((x.bits.toNat >>> (fmt.width - 1 - fmt.expBits)) % 2 ^ fmt.expBits)
      (x.bits.toNat % 2 ^ (fmt.width - 1 - fmt.expBits)) := by
  have hw : 1 ≤ fmt.width := by cases fmt <;> decide
  have hEb : fmt.expBits ≤ fmt.width - 1 := by cases fmt <;> decide
  obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec fmt (!x.bits.msb)
    (Nat.mod_lt _ (Nat.two_pow_pos fmt.expBits)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  apply Float.eq_of_fields
  · have hb : (Float.neg x).bits = x.bits ^^^ BitVec.ofNat fmt.width (1 <<< (fmt.width - 1)) := by
      unfold Float.neg
      rw [BitVec.ofNat_xor, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hp : (2 : Nat) ^ (fmt.width - 1) < 2 ^ fmt.width :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have htop : (BitVec.ofNat fmt.width (1 <<< (fmt.width - 1))).msb = true := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.one_shiftLeft, Nat.mod_eq_of_lt hp]
      simp
    rw [hmsb, hb, BitVec.msb_xor, htop]
    simp
  · rw [hexpEq, neg_bits_toNat, xor_top_field (by omega)]
  · rw [hrestEq, neg_bits_toNat]
    have := xor_top_field (v := x.bits.toNat) (w := fmt.width) (R := 0)
      (k := fmt.width - 1 - fmt.expBits) (by omega)
    simpa using this

private theorem classify_pack_neg {fmt : FloatFmt} (s : Bool) {E F : Nat}
    (hE : E < 2 ^ fmt.expBits) (hF : F < 2 ^ (fmt.width - 1 - fmt.expBits)) :
    (Float.pack fmt (!s) E F).classify = match (Float.pack fmt s E F).classify with
      | .nan => .nan
      | .inf t => .inf (!t)
      | .finite t m e => .finite (!t) m e := by
  by_cases hf80 : fmt = .f80
  · subst hf80
    rw [restW_eq_fracBits_succ_f80] at hF
    rw [classify_pack_f80' s hE hF, classify_pack_f80' (!s) hE hF]
    by_cases h1 : E = 2 ^ FloatFmt.f80.expBits - 1 <;> by_cases h2 : F / 2 ^ 63 = 0 <;>
      by_cases h3 : F % 2 ^ 63 = 0 <;> by_cases h4 : E = 0 <;>
      simp [h1, h2, h3, h4, show (0 : Nat) ≠ 2 ^ FloatFmt.f80.expBits - 1 by decide]
  · rw [restW_eq_fracBits fmt hf80] at hF
    rw [classify_pack_of_ne_f80' hf80 s hE hF, classify_pack_of_ne_f80' hf80 (!s) hE hF]
    by_cases h1 : E = 2 ^ fmt.expBits - 1 <;> by_cases h2 : F = 0 <;> by_cases h4 : E = 0 <;>
      simp [h1, h2, h4, show (0 : Nat) ≠ 2 ^ fmt.expBits - 1 by cases fmt <;> decide]

/-- `neg` flips the sign of the class and keeps NaN a NaN. -/
theorem classify_neg {fmt : FloatFmt} (x : Float fmt) :
    (Float.neg x).classify = match x.classify with
      | .nan => .nan
      | .inf t => .inf (!t)
      | .finite t m e => .finite (!t) m e := by
  rw [neg_eq_pack x]
  conv => rhs; rw [Float.eq_pack_fields x]
  exact classify_pack_neg _ (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem toRat?_neg {fmt : FloatFmt} {x : Float fmt} {a : Rat} (h : x.toRat? = some a) :
    (Float.neg x).toRat? = some (-a) := by
  obtain ⟨s, m, e, hc, rfl⟩ := exists_finite_of_toRat? h
  unfold Float.toRat?
  rw [classify_neg, hc]
  cases s <;> simp [finiteToRat]

theorem isNaN_neg {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = true) :
    (Float.neg x).isNaN = true := by
  rw [isNaN_iff, classify_neg, (isNaN_iff x).mp h]

/-- **Finite closure and error of `-`.** Finite operands whose exact difference has magnitude
at most `A < 2^emax` subtract to a finite value within `u·A + η` of the exact difference
(`Float.sub x y` is `x + (-y)` by definition). -/
theorem sub_error {fmt : FloatFmt} {x y : Float fmt} {a b A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hlo : -A ≤ a - b) (hhi : a - b ≤ A)
    (hov : A < fmt.overflowBound) :
    ∃ r, (Float.sub x y).toRat? = some r ∧
      r - (a - b) ≤ fmt.unitRoundoff * A + fmt.underflowError ∧
      (a - b) - r ≤ fmt.unitRoundoff * A + fmt.underflowError := by
  rw [Rat.sub_eq_add_neg a b] at hlo hhi ⊢
  exact add_error hx (toRat?_neg hy) hlo hhi hov

/-! ## `/` -/

/-- **Finite closure and error of `/`.** Finite operands with a nonzero divisor whose exact
quotient has magnitude at most `A < 2^emax` divide to a finite value within `u·A + η` of the
exact quotient. `b ≠ 0` is needed: a zero divisor gives an infinity, or NaN for `0 / 0`. -/
theorem div_error {fmt : FloatFmt} {x y : Float fmt} {a b A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hb : b ≠ 0) (hlo : -A ≤ a / b) (hhi : a / b ≤ A)
    (hov : A < fmt.overflowBound) :
    ∃ r, (Float.div x y).toRat? = some r ∧
      r - a / b ≤ fmt.unitRoundoff * A + fmt.underflowError ∧
      a / b - r ≤ fmt.unitRoundoff * A + fmt.underflowError := by
  obtain ⟨sa, ma, ea, hxc, rfl⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, rfl⟩ := exists_finite_of_toRat? hy
  have hmb : mb ≠ 0 := fun h => hb (by rw [h, finiteToRat_zero])
  rw [div_of_finite hxc hyc hmb]
  refine roundRat_error fmt (fun hq => ?_) hlo hhi hov
  have hma : ma ≠ 0 := fun h => hq (by rw [h, finiteToRat_zero, Rat.div_def, Rat.zero_mul])
  have hinv : ∀ q : Rat, (-q)⁻¹ = -q⁻¹ := fun q => by grind
  have hpa := finiteToRat_false_pos hma ea
  have hpb := Rat.inv_pos.mpr (finiteToRat_false_pos hmb eb)
  have hpp := Rat.mul_pos hpa hpb
  rw [Rat.div_def] at hq ⊢
  by_cases hlt : finiteToRat sa ma ea * (finiteToRat sb mb eb)⁻¹ < 0
  · rw [decide_eq_true hlt]
    cases sa <;> cases sb <;> (try simp only [finiteToRat_true_eq, hinv] at hlt) <;>
      first | rfl | (exfalso; grind)
  · rw [decide_eq_false hlt]
    cases sa <;> cases sb <;> (try simp only [finiteToRat_true_eq, hinv] at hlt) <;>
      first | rfl | (exfalso; grind)

/-! ## `@floatCast` -/

/-- **Finite closure and error of `@floatCast`.** A finite value of magnitude at most `A`,
`A` below the target format's `2^emax`, converts to a finite value within `u·A + η` of it
(the target format's constants). -/
theorem conv_error {fmt fmt2 : FloatFmt} {x : Float fmt} {a A : Rat} (hx : x.toRat? = some a)
    (hlo : -A ≤ a) (hhi : a ≤ A) (hov : A < fmt2.overflowBound) :
    ∃ r, (Float.conv fmt2 x).toRat? = some r ∧
      r - a ≤ fmt2.unitRoundoff * A + fmt2.underflowError ∧
      a - r ≤ fmt2.unitRoundoff * A + fmt2.underflowError := by
  obtain ⟨s, m, e, hxc, rfl⟩ := exists_finite_of_toRat? hx
  unfold Float.conv
  rw [hxc]
  refine roundRat_error fmt2 (fun hq => ?_) hlo hhi hov
  have hm : m ≠ 0 := fun h => hq (by rw [h, finiteToRat_zero])
  have := finiteToRat_lt_zero_iff s hm e
  cases s <;> simp_all

/-! ## `@mulAdd` -/

/-- `fma` of three finite operands: one rounding of the exact `a·b + c` at the format's own
rounding schedule, with a sign that matches the exact value whenever it is nonzero. -/
private theorem fma_of_finite {fmt : FloatFmt} {x y z : Float fmt} {sa sb sc : Bool}
    {ma mb mc : Nat} {ea eb ec : Int} (hxc : x.classify = .finite sa ma ea)
    (hyc : y.classify = .finite sb mb eb) (hzc : z.classify = .finite sc mc ec) :
    ∃ neg : Bool, (finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec ≠ 0 →
        neg = decide (finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec < 0)) ∧
      Float.fma x y z =
        if h : fmt = .f16 then h ▸ Float.conv .f16 (Float.roundRat .f32 neg
          (finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec))
        else if h : fmt = .f80 then h ▸ Float.conv .f80 (Float.roundRat .f128 neg
          (finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec))
        else Float.roundRat fmt neg
          (finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec) := by
  refine ⟨if finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec = 0 then
      ((sa != sb) && (ma == 0 || mb == 0)) && (sc && mc == 0)
    else decide (finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec < 0),
    fun hq => by simp only [hq, ↓reduceIte], ?_⟩
  unfold Float.fma
  rw [hxc, hyc, hzc]

/-- **Finite closure and error of `@mulAdd`** for `f32`, `f64` and `f128`, which round once:
finite operands whose exact `a·b + c` has magnitude at most `A < 2^emax` give a finite value
within `u·A + η` of it. -/
theorem fma_error {fmt : FloatFmt} (h16 : fmt ≠ .f16) (h80 : fmt ≠ .f80) {x y z : Float fmt}
    {a b c A : Rat} (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (hlo : -A ≤ a * b + c) (hhi : a * b + c ≤ A) (hov : A < fmt.overflowBound) :
    ∃ r, (Float.fma x y z).toRat? = some r ∧
      r - (a * b + c) ≤ fmt.unitRoundoff * A + fmt.underflowError ∧
      (a * b + c) - r ≤ fmt.unitRoundoff * A + fmt.underflowError := by
  obtain ⟨sa, ma, ea, hxc, rfl⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, rfl⟩ := exists_finite_of_toRat? hy
  obtain ⟨sc, mc, ec, hzc, rfl⟩ := exists_finite_of_toRat? hz
  obtain ⟨neg, hneg, heq⟩ := fma_of_finite hxc hyc hzc
  rw [heq, dite_eq_right h16, dite_eq_right h80]
  exact roundRat_error fmt hneg hlo hhi hov

/-- Two roundings: to `mid`, then `@floatCast` to `fmt`. The errors add up; the second is
relative to the bound `A' = A + u_mid·A + η_mid` of the intermediate value. -/
private theorem roundRat_conv_error (fmt mid : FloatFmt) {neg : Bool} {q A : Rat}
    (hsign : q ≠ 0 → neg = decide (q < 0)) (hlo : -A ≤ q) (hhi : q ≤ A)
    (hovm : A < mid.overflowBound)
    (hov : A + (mid.unitRoundoff * A + mid.underflowError) < fmt.overflowBound) :
    ∃ r, (Float.conv fmt (Float.roundRat mid neg q)).toRat? = some r ∧
      r - q ≤ (mid.unitRoundoff * A + mid.underflowError) +
        (fmt.unitRoundoff * (A + (mid.unitRoundoff * A + mid.underflowError)) +
          fmt.underflowError) ∧
      q - r ≤ (mid.unitRoundoff * A + mid.underflowError) +
        (fmt.unitRoundoff * (A + (mid.unitRoundoff * A + mid.underflowError)) +
          fmt.underflowError) := by
  obtain ⟨r1, hr1, e1, e2⟩ := roundRat_error mid hsign hlo hhi hovm
  obtain ⟨r, hr, e3, e4⟩ := conv_error (fmt2 := fmt) hr1
    (A := A + (mid.unitRoundoff * A + mid.underflowError)) (by grind) (by grind) hov
  exact ⟨r, hr, by grind, by grind⟩

/-- **`@mulAdd` on `f16`**: rounded to `f32`, then to `f16` (`docs/floats.md` §Semantics). The
error is that of the two roundings, the second relative to `A' = A + u₃₂·A + η₃₂`. -/
theorem fma_error_f16 {x y z : Float .f16} {a b c A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hz : z.toRat? = some c) (hlo : -A ≤ a * b + c)
    (hhi : a * b + c ≤ A) (hov32 : A < FloatFmt.f32.overflowBound)
    (hov : A + (FloatFmt.f32.unitRoundoff * A + FloatFmt.f32.underflowError) <
      FloatFmt.f16.overflowBound) :
    ∃ r, (Float.fma x y z).toRat? = some r ∧
      r - (a * b + c) ≤ (FloatFmt.f32.unitRoundoff * A + FloatFmt.f32.underflowError) +
        (FloatFmt.f16.unitRoundoff * (A + (FloatFmt.f32.unitRoundoff * A +
          FloatFmt.f32.underflowError)) + FloatFmt.f16.underflowError) ∧
      (a * b + c) - r ≤ (FloatFmt.f32.unitRoundoff * A + FloatFmt.f32.underflowError) +
        (FloatFmt.f16.unitRoundoff * (A + (FloatFmt.f32.unitRoundoff * A +
          FloatFmt.f32.underflowError)) + FloatFmt.f16.underflowError) := by
  obtain ⟨sa, ma, ea, hxc, rfl⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, rfl⟩ := exists_finite_of_toRat? hy
  obtain ⟨sc, mc, ec, hzc, rfl⟩ := exists_finite_of_toRat? hz
  obtain ⟨neg, hneg, heq⟩ := fma_of_finite hxc hyc hzc
  rw [heq, dite_eq_left rfl]
  exact roundRat_conv_error .f16 .f32 hneg hlo hhi hov32 hov

/-- **`@mulAdd` on `f80`**: rounded to `f128`, then to `f80` (`docs/floats.md` §Semantics). The
error is that of the two roundings, the second relative to `A' = A + u₁₂₈·A + η₁₂₈`. -/
theorem fma_error_f80 {x y z : Float .f80} {a b c A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hz : z.toRat? = some c) (hlo : -A ≤ a * b + c)
    (hhi : a * b + c ≤ A) (hov128 : A < FloatFmt.f128.overflowBound)
    (hov : A + (FloatFmt.f128.unitRoundoff * A + FloatFmt.f128.underflowError) <
      FloatFmt.f80.overflowBound) :
    ∃ r, (Float.fma x y z).toRat? = some r ∧
      r - (a * b + c) ≤ (FloatFmt.f128.unitRoundoff * A + FloatFmt.f128.underflowError) +
        (FloatFmt.f80.unitRoundoff * (A + (FloatFmt.f128.unitRoundoff * A +
          FloatFmt.f128.underflowError)) + FloatFmt.f80.underflowError) ∧
      (a * b + c) - r ≤ (FloatFmt.f128.unitRoundoff * A + FloatFmt.f128.underflowError) +
        (FloatFmt.f80.unitRoundoff * (A + (FloatFmt.f128.unitRoundoff * A +
          FloatFmt.f128.underflowError)) + FloatFmt.f80.underflowError) := by
  obtain ⟨sa, ma, ea, hxc, rfl⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, rfl⟩ := exists_finite_of_toRat? hy
  obtain ⟨sc, mc, ec, hzc, rfl⟩ := exists_finite_of_toRat? hz
  obtain ⟨neg, hneg, heq⟩ := fma_of_finite hxc hyc hzc
  rw [heq, dite_eq_right (by decide), dite_eq_left rfl]
  exact roundRat_conv_error .f80 .f128 hneg hlo hhi hov128 hov

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

theorem sub_isNaN_left {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    (Float.sub x y).isNaN = true :=
  add_isNaN_left h _

theorem sub_isNaN_right {fmt : FloatFmt} (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    (Float.sub x y).isNaN = true :=
  add_isNaN_right x (isNaN_neg h)

theorem div_isNaN_left {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    (Float.div x y).isNaN = true := by
  unfold Float.div
  rw [(isNaN_iff x).mp h]
  exact isNaN_nan

theorem div_isNaN_right {fmt : FloatFmt} (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    (Float.div x y).isNaN = true := by
  unfold Float.div
  rw [(isNaN_iff y).mp h]
  cases x.classify <;> exact isNaN_nan

/-- `@mulAdd` propagates NaN from any operand (all formats, both rounding schedules). -/
theorem fma_isNaN {fmt : FloatFmt} {x y z : Float fmt}
    (h : x.isNaN = true ∨ y.isNaN = true ∨ z.isNaN = true) : (Float.fma x y z).isNaN = true := by
  unfold Float.fma
  rcases h with h | h | h <;> rw [(isNaN_iff _).mp h]
  · exact isNaN_nan
  · cases x.classify <;> exact isNaN_nan
  · cases x.classify <;> cases y.classify <;> exact isNaN_nan

theorem sqrt_isNaN {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = true) :
    (Float.sqrt x).isNaN = true := by
  unfold Float.sqrt Float.sqrt.sqrtCore
  rw [(isNaN_iff x).mp h]
  exact isNaN_nan

/-- `@sqrt` of a negative nonzero finite value is NaN. -/
theorem sqrt_isNaN_of_neg {fmt : FloatFmt} {x : Float fmt} {a : Rat} (hx : x.toRat? = some a)
    (ha : a < 0) : (Float.sqrt x).isNaN = true := by
  obtain ⟨s, m, e, hc, rfl⟩ := exists_finite_of_toRat? hx
  have hm : m ≠ 0 := fun h => by rw [h, finiteToRat_zero] at ha; exact Rat.lt_irrefl ha
  have hs : s = true := (finiteToRat_lt_zero_iff s hm e).mp ha
  subst hs
  unfold Float.sqrt Float.sqrt.sqrtCore
  rw [hc]
  simp only [hm, ↓reduceIte]
  exact isNaN_nan

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

/-! ## `@sqrt` -/

private theorem sqrt_round_bounds (S M : Nat)
    (hM : M = if S - S.sqrt * S.sqrt ≤ S.sqrt then S.sqrt else S.sqrt + 1) :
    4 * S ≤ (2 * M + 1) * (2 * M + 1) ∧ (0 < S → 1 ≤ M ∧ (2 * M - 1) * (2 * M - 1) ≤ 4 * S) ∧
      M ≤ S.sqrt + 1 := by
  have h1 := Nat.sqrt_le S
  have h2 := Nat.lt_succ_sqrt S
  obtain ⟨r, hr⟩ : ∃ r, S.sqrt = r := ⟨_, rfl⟩
  rw [hr] at h1 h2 hM ⊢
  split at hM <;> rw [hM]
  · refine ⟨by grind, fun hS => ⟨?_, ?_⟩, by omega⟩
    · rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at h2; omega
      · omega
    · rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at h2; omega
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        grind
  · refine ⟨by grind, fun _ => ⟨by omega, by grind⟩, by omega⟩

private theorem sq_lt_sq {c s : Rat} (hc : 0 ≤ c) (h : c < s) : c * c < s * s := by
  have h1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h) hc
  have h2 := Rat.mul_lt_mul_of_pos_right h (by grind : (0 : Rat) < s)
  grind

/-- The rounding step of `sqrtCore` for a positive finite `m·2^e`, with its exponent `te`,
scaled radicand `S = m·2^(e - 2·te)` and rounded root `M` named: the result is finite and
nonnegative, and within `u·A + η` of `√(m·2^e)` for every `A ≥ 0` with `m·2^e ≤ A²`, stated
without irrationals: `s - r ≤ u·A + η` for `s² ≤ m·2^e`, `r - s ≤ u·A + η` for `m·2^e ≤ s²`. -/
private theorem sqrt_final (fmt : FloatFmt) {m S M : Nat} {e te : Int} (hm : m ≠ 0)
    (hmlt : m < 2 ^ fmt.prec) (hlo : fmt.emin - fmt.fracBits ≤ e)
    (hhi : e + (fmt.prec - 1 : Int) ≤ fmt.emax)
    (hte : te = Min.min (Max.max (((Nat.log2 m : Int) + e).ediv 2 - ((fmt.prec : Int) - 1))
      (fmt.emin - ((fmt.prec : Int) - 1))) (e.ediv 2))
    (hS : S = m <<< (e - 2 * te).toNat)
    (hM : M = if S - S.sqrt * S.sqrt ≤ S.sqrt then S.sqrt else S.sqrt + 1)
    {A : Rat} (hA : 0 ≤ A) (haA : finiteToRat false m e ≤ A * A) :
    ∃ r, (Float.finalizeRounded fmt false (M : Int) te).toRat? = some r ∧ 0 ≤ r ∧
      (∀ s, 0 ≤ s → s * s ≤ finiteToRat false m e →
        s - r ≤ fmt.unitRoundoff * A + fmt.underflowError) ∧
      (∀ s, 0 ≤ s → finiteToRat false m e ≤ s * s →
        r - s ≤ fmt.unitRoundoff * A + fmt.underflowError) := by
  have hpf : ((fmt.prec : Int) - 1) = fmt.fracBits := by simp only [FloatFmt.prec]; omega
  have hp1 : 1 ≤ fmt.prec := by cases fmt <;> decide
  have hfb : 1 ≤ fmt.fracBits := by cases fmt <;> decide
  have hY0 : fmt.emin - fmt.fracBits ≤ 0 := by cases fmt <;> decide
  have hemax : 2 ≤ fmt.emax := by cases fmt <;> decide
  have hemin : fmt.emin + 1 ≤ fmt.emax := by cases fmt <;> decide
  have hL : (Nat.log2 m : Int) ≤ fmt.fracBits := by
    have := (Nat.log2_lt hm).mpr hmlt
    simp only [FloatFmt.prec] at this; omega
  have hediv : ∀ x : Int, x.ediv 2 = x / 2 := fun _ => rfl
  simp only [hediv, hpf] at hte
  generalize hL' : (Nat.log2 m : Int) = L at hL hte
  -- `sqrtCore`'s outer `min` never binds: `te` is the clamped `max`.
  have hte' : te = Max.max ((L + e) / 2 - fmt.fracBits) (fmt.emin - fmt.fracBits) := by omega
  have hk0 : 0 ≤ e - 2 * te := by omega
  generalize hk : (e - 2 * te).toNat = k at hS
  have hS' : S = m * 2 ^ k := by rw [hS, Nat.shiftLeft_eq]
  have hSpos : 0 < S := by rw [hS']; exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  obtain ⟨hb1, hb2, hb3⟩ := sqrt_round_bounds S M hM
  obtain ⟨hM1, hb2⟩ := hb2 hSpos
  -- `M ≤ 2^prec`: the root of a radicand below `2^(2·prec)`.
  have hroot : S.sqrt < 2 ^ fmt.prec := by
    apply sqrt_lt_of_lt_mul
    have h2p : (2 : Nat) ^ (2 * fmt.prec) = 2 ^ fmt.prec * 2 ^ fmt.prec := by
      rw [Nat.two_mul, Nat.pow_add]
    rw [← h2p, hS]
    rw [← hk]
    apply sqrt_shiftedM_lt (p := fmt.prec) <;> (try simp only [hpf, hL']) <;> omega
  have hMle : (M : Int) ≤ 2 ^ fmt.prec := by
    have : M ≤ 2 ^ fmt.prec := by omega
    exact_mod_cast this
  -- Normal, or at the subnormal exponent.
  have hnorm : 2 ^ fmt.fracBits ≤ (M : Int) ∨ te = fmt.emin - fmt.fracBits := by
    by_cases hY : te = fmt.emin - fmt.fracBits
    · exact Or.inr hY
    · left
      have hX : te = (L + e) / 2 - fmt.fracBits := by omega
      have hlog : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
      have hLk : 2 * fmt.fracBits ≤ m.log2 + k := by omega
      have hS2 : 2 ^ fmt.fracBits * 2 ^ fmt.fracBits ≤ S := by
        rw [← Nat.pow_add, hS', ← Nat.two_mul]
        calc 2 ^ (2 * fmt.fracBits) ≤ 2 ^ (m.log2 + k) := Nat.pow_le_pow_right (by decide) hLk
          _ = 2 ^ m.log2 * 2 ^ k := Nat.pow_add _ _ _
          _ ≤ m * 2 ^ k := Nat.mul_le_mul_right _ hlog
      have hsq : 2 ^ fmt.fracBits ≤ S.sqrt := by
        apply Nat.not_lt.mp
        intro hlt
        have h1 := Nat.lt_succ_sqrt S
        have h2 : S.sqrt.succ * S.sqrt.succ ≤ 2 ^ fmt.fracBits * 2 ^ fmt.fracBits :=
          Nat.mul_le_mul hlt hlt
        omega
      have : 2 ^ fmt.fracBits ≤ M := by
        rw [hM]; split <;> omega
      have hc : ((2 ^ fmt.fracBits : Nat) : Int) = (2 : Int) ^ fmt.fracBits := by push_cast; rfl
      rw [← hc]; exact_mod_cast this
  have hov : te + fmt.prec ≤ fmt.emax := by simp only [FloatFmt.prec] at hhi ⊢; omega
  obtain ⟨r, hr⟩ := finalizeRounded_isSome fmt false hMle (by omega) hnorm hov
  have hrv := finalizeRounded_toRat fmt false hMle (by omega) hnorm hr
  rw [Int.toNat_natCast, finiteToRat_false_eq_zpow] at hrv
  refine ⟨r, hr, ?_⟩
  -- Values: `r = M·P`, `m·2^e = S·P·P` with `P = 2^te`.
  have hP := two_zpow_pos te
  have ha : finiteToRat false m e = (S : Rat) * (2 : Rat) ^ te * (2 : Rat) ^ te := by
    rw [finiteToRat_false_eq_zpow, hS']
    have he : e = (k : Int) + te + te := by omega
    rw [he, Rat.zpow_add (by decide), Rat.zpow_add (by decide), Rat.zpow_natCast]
    push_cast
    grind
  have hu := FloatFmt.unitRoundoff_pos fmt
  have hη := FloatFmt.underflowError_pos fmt
  have huA := Rat.mul_nonneg (Rat.le_of_lt hu) hA
  -- `2^te ≤ 2·(u·A + η)`: `2η` at the subnormal exponent, else `2u·2^⌊(L+e)/2⌋ ≤ 2u·A`.
  have hPb : (2 : Rat) ^ te ≤ 2 * (fmt.unitRoundoff * A + fmt.underflowError) := by
    by_cases hY : te = fmt.emin - fmt.fracBits
    · have : te = (fmt.emin - fmt.prec) + 1 := by simp only [FloatFmt.prec]; omega
      rw [this, Rat.zpow_add_one (by decide)]
      unfold FloatFmt.underflowError at hη ⊢
      grind
    · have hQ : (2 : Rat) ^ ((L + e) / 2) ≤ A := by
        apply Rat.not_lt.mp
        intro hlt
        have h1 := sq_lt_sq hA hlt
        have h2 : (2 : Rat) ^ ((L + e) / 2) * (2 : Rat) ^ ((L + e) / 2) ≤ (2 : Rat) ^ (L + e) := by
          rw [← Rat.zpow_add (by decide)]; exact two_zpow_le (by omega)
        have h3 : (2 : Rat) ^ (L + e) ≤ finiteToRat false m e := by
          rw [finiteToRat_false_eq_zpow, Rat.zpow_add (by decide), ← hL', Rat.zpow_natCast]
          have : ((2 ^ m.log2 : Nat) : Rat) ≤ (m : Rat) :=
            Rat.natCast_le_natCast.mpr (Nat.log2_self_le hm)
          push_cast at this
          exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (two_zpow_pos e))
        grind
      have : te = ((L + e) / 2 + -(fmt.prec : Int)) + 1 := by simp only [FloatFmt.prec]; omega
      rw [this, Rat.zpow_add_one (by decide), Rat.zpow_add (by decide)]
      have h2 := Rat.mul_le_mul_of_nonneg_right hQ (Rat.le_of_lt hu)
      unfold FloatFmt.unitRoundoff at h2 hu huA ⊢
      grind
  rw [ha] at haA ⊢
  generalize (2 : Rat) ^ te = P at hP hrv ha hPb
  have hPP := Rat.mul_nonneg (Rat.le_of_lt hP) (Rat.le_of_lt hP)
  have hM0 : (0 : Rat) ≤ M := Rat.natCast_nonneg
  refine ⟨?_, fun s hs hsa => ?_, fun s hs hsa => ?_⟩
  · rw [hrv]; exact Rat.mul_nonneg hM0 (Rat.le_of_lt hP)
  · -- `s ≤ (M + 1/2)·P`, since `S ≤ (M + 1/2)²`.
    apply Rat.not_lt.mp
    intro hgt
    have hc0 : 0 ≤ ((M : Rat) + 1 / 2) * P := Rat.mul_nonneg (by grind) (Rat.le_of_lt hP)
    have hlt : ((M : Rat) + 1 / 2) * P < s := by grind
    have h1 := sq_lt_sq hc0 hlt
    have hb1' : (4 : Rat) * S ≤ (2 * M + 1) * (2 * M + 1) := by exact_mod_cast hb1
    have h2 := Rat.mul_le_mul_of_nonneg_right hb1' hPP
    grind
  · -- `(M - 1/2)·P ≤ s`, since `(M - 1/2)² ≤ S`.
    apply Rat.not_lt.mp
    intro hgt
    have hM1' : (1 : Rat) ≤ M := by exact_mod_cast hM1
    have hc0 : 0 ≤ ((M : Rat) - 1 / 2) * P := Rat.mul_nonneg (by grind) (Rat.le_of_lt hP)
    have hlt : s < ((M : Rat) - 1 / 2) * P := by grind
    have h1 := sq_lt_sq hs hlt
    have hb2' : ((2 * M - 1 : Nat) : Rat) * ((2 * M - 1 : Nat) : Rat) ≤ 4 * S := by
      exact_mod_cast hb2
    have hcast : ((2 * M - 1 : Nat) : Rat) = 2 * M - 1 := by
      have : 2 * M - 1 + 1 = 2 * M := by omega
      have h := congrArg (fun n : Nat => (n : Rat)) this
      push_cast at h
      grind
    rw [hcast] at hb2'
    have h2 := Rat.mul_le_mul_of_nonneg_right hb2' hPP
    grind

/-- **Finite closure and error of `@sqrt`.** A finite operand with value `a ≥ 0` (also `-0`)
has a finite, nonnegative square root `r`. For every `A ≥ 0` with `a ≤ A²`, `r` is within
`u·A + η` of `√a`; since `√a` is in general irrational, both sides are stated through
squares: `s - r ≤ u·A + η` for every `s ≥ 0` with `s² ≤ a`, and `r - s ≤ u·A + η` for
every `s ≥ 0` with `a ≤ s²`. No overflow condition: the root of a finite value is finite. A
negative nonzero operand gives NaN (`sqrt_isNaN_of_neg`). -/
theorem sqrt_error {fmt : FloatFmt} {x : Float fmt} {a A : Rat} (hx : x.toRat? = some a)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (haA : a ≤ A * A) :
    ∃ r, (Float.sqrt x).toRat? = some r ∧ 0 ≤ r ∧
      (∀ s, 0 ≤ s → s * s ≤ a → s - r ≤ fmt.unitRoundoff * A + fmt.underflowError) ∧
      (∀ s, 0 ≤ s → a ≤ s * s → r - s ≤ fmt.unitRoundoff * A + fmt.underflowError) := by
  have hu := FloatFmt.unitRoundoff_pos fmt
  have hη := FloatFmt.underflowError_pos fmt
  have huA := Rat.mul_nonneg (Rat.le_of_lt hu) hA
  obtain ⟨sg, m, e, hc, rfl⟩ := exists_finite_of_toRat? hx
  unfold Float.sqrt Float.sqrt.sqrtCore
  rw [hc]
  by_cases hm : m = 0
  · subst hm
    simp only [↓reduceIte, finiteToRat_zero]
    refine ⟨0, by simp [Float.toRat?, classify_zero, finiteToRat_zero], Rat.le_refl,
      fun s hs hss => ?_, fun s hs _ => by grind⟩
    rcases Rat.le_iff_lt_or_eq.mp hs with hpos | hz
    · have := sq_lt_sq Rat.le_refl hpos
      grind
    · grind
  have hsg : sg = false := by
    cases sg
    · rfl
    · exfalso
      have := (finiteToRat_lt_zero_iff true hm e).mpr rfl
      grind
  subst hsg
  simp only [hm, ↓reduceIte, Bool.false_eq_true]
  obtain ⟨hlo, hhi, -⟩ := classify_finite_range hc
  obtain ⟨r, hr, h0, h1, h2⟩ := sqrt_final fmt hm (classify_mantissa_lt hc) hlo hhi rfl rfl rfl
    hA haA
  refine ⟨r, ?_, h0, h1, h2⟩
  rw [← hr]
  congr 1
  split <;> simp

/-! ## `compiler-rt` helpers

The `--float-semantics compiler-rt` ports (`CompilerRt.lean`, `docs/floats.md` groups A, B,
E–H) for which a bound follows from the IEEE lemmas above. The other ports stay out of scope:
see `docs/floats.md` §Numerical bounds. -/

/-- `@floatCast` to a format with at least the precision and exponent range is exact. -/
theorem conv_toRat_of_wider {fmt fmt2 : FloatFmt} (hp : fmt.fracBits ≤ fmt2.fracBits)
    (hlo : fmt2.emin - fmt2.fracBits ≤ fmt.emin - fmt.fracBits)
    (hhi : fmt.emax - fmt.fracBits ≤ fmt2.emax - fmt2.fracBits) {x : Float fmt} {a : Rat}
    (hx : x.toRat? = some a) : (Float.conv fmt2 x).toRat? = some a := by
  obtain ⟨s, m, e, hc, rfl⟩ := exists_finite_of_toRat? hx
  unfold Float.conv
  rw [hc]
  by_cases hm : m = 0
  · subst hm
    simp [Float.toRat?, classify_zero, finiteToRat_zero]
  obtain ⟨he_lo, he_hi, -⟩ := classify_finite_range hc
  have hmlt := classify_mantissa_lt hc
  have hmlt2 : m < 2 ^ fmt2.prec :=
    Nat.lt_of_lt_of_le hmlt (Nat.pow_le_pow_right (by decide) (by simp only [FloatFmt.prec]; omega))
  exact roundRat_finiteToRat_toRat fmt2 s s (Nat.pos_of_ne_zero hm) hmlt2 (by omega)
    (by simp only [FloatFmt.prec] at he_hi ⊢; omega)

/-- **`@mulAdd` on `f32`, `compiler-rt` (`fmaf`).** The port computes the product in `f64`, adds
`c` in `f64` and rounds to `f32`: three roundings. With `|a·b| ≤ B`, `|a·b + c| ≤ A`,
`e₁ = u₆₄·B + η₆₄`, `A₁ = A + e₁`, `e₂ = u₆₄·A₁ + η₆₄` and `A₂ = A₁ + e₂`, the result is
finite and within `e₁ + e₂ + u₃₂·A₂ + η₃₂` of `a·b + c` when `B, A₁ < 2^1023` and
`A₂ < 2^127`. -/
theorem fmaRt_error_f32 {x y z : Float .f32} {a b c B A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hz : z.toRat? = some c) (hblo : -B ≤ a * b) (hbhi : a * b ≤ B)
    (hlo : -A ≤ a * b + c) (hhi : a * b + c ≤ A)
    (hovB : B < FloatFmt.f64.overflowBound)
    (hov1 : A + (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError) <
      FloatFmt.f64.overflowBound)
    (hov2 : A + (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError) +
      (FloatFmt.f64.unitRoundoff * (A + (FloatFmt.f64.unitRoundoff * B +
        FloatFmt.f64.underflowError)) + FloatFmt.f64.underflowError) <
      FloatFmt.f32.overflowBound) :
    ∃ r, (Float.fmaRt x y z).toRat? = some r ∧
      r - (a * b + c) ≤ (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError) +
        (FloatFmt.f64.unitRoundoff * (A + (FloatFmt.f64.unitRoundoff * B +
          FloatFmt.f64.underflowError)) + FloatFmt.f64.underflowError) +
        (FloatFmt.f32.unitRoundoff * (A + (FloatFmt.f64.unitRoundoff * B +
          FloatFmt.f64.underflowError) + (FloatFmt.f64.unitRoundoff * (A +
            (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError)) +
              FloatFmt.f64.underflowError)) + FloatFmt.f32.underflowError) ∧
      (a * b + c) - r ≤ (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError) +
        (FloatFmt.f64.unitRoundoff * (A + (FloatFmt.f64.unitRoundoff * B +
          FloatFmt.f64.underflowError)) + FloatFmt.f64.underflowError) +
        (FloatFmt.f32.unitRoundoff * (A + (FloatFmt.f64.unitRoundoff * B +
          FloatFmt.f64.underflowError) + (FloatFmt.f64.unitRoundoff * (A +
            (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError)) +
              FloatFmt.f64.underflowError)) + FloatFmt.f32.underflowError) := by
  have hw {w : Float .f32} {v : Rat} (h : w.toRat? = some v) :
      (Float.conv .f64 w).toRat? = some v :=
    conv_toRat_of_wider (by decide) (by decide) (by decide) h
  have hu := Rat.le_of_lt (FloatFmt.unitRoundoff_pos .f64)
  have hη := Rat.le_of_lt (FloatFmt.underflowError_pos .f64)
  have huB := Rat.mul_nonneg hu (show 0 ≤ B by grind)
  obtain ⟨p, hp, p1, p2⟩ := mul_error (hw hx) (hw hy) hblo hbhi hovB
  obtain ⟨q, hq, q1, q2⟩ := add_error hp (hw hz)
    (A := A + (FloatFmt.f64.unitRoundoff * B + FloatFmt.f64.underflowError))
    (by grind) (by grind) hov1
  have huA := Rat.mul_nonneg hu (show 0 ≤ A + (FloatFmt.f64.unitRoundoff * B +
    FloatFmt.f64.underflowError) by grind)
  obtain ⟨r, hr, r1, r2⟩ := conv_error (fmt2 := .f32) hq (by grind) (by grind) hov2
  exact ⟨r, (rfl : Float.fmaRt x y z = _) ▸ hr, by grind, by grind⟩

/-- **`/` on `f128`, `compiler-rt` before Zig 0.16.0 (`__divtf3`, group A).** The port flushes a
nonzero subnormal quotient to a signed zero, so the error of `div_error` grows by at most the
smallest normal magnitude `2^emin` (`2^-16382`). -/
theorem divRt_error_f128 {x y : Float .f128} {a b A : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hb : b ≠ 0) (hlo : -A ≤ a / b) (hhi : a / b ≤ A)
    (hov : A < FloatFmt.f128.overflowBound) :
    ∃ r, (Float.divRt x y).toRat? = some r ∧
      r - a / b ≤ FloatFmt.f128.unitRoundoff * A + FloatFmt.f128.underflowError +
        (2 : Rat) ^ FloatFmt.f128.emin ∧
      a / b - r ≤ FloatFmt.f128.unitRoundoff * A + FloatFmt.f128.underflowError +
        (2 : Rat) ^ FloatFmt.f128.emin := by
  obtain ⟨q, hq, e1, e2⟩ := div_error hx hy hb hlo hhi hov
  have hm2 := two_zpow_pos FloatFmt.f128.emin
  obtain ⟨s, m, e, hc, rfl⟩ := exists_finite_of_toRat? hq
  show ∃ r, (match (Float.div x y).classify with
    | .finite s m _ => if m ≠ 0 ∧ m < 2 ^ FloatFmt.f128.fracBits then Float.zero s
        else Float.div x y
    | _ => Float.div x y).toRat? = some r ∧ _
  rw [hc]
  simp only []
  by_cases hsub : m ≠ 0 ∧ m < 2 ^ FloatFmt.f128.fracBits
  · rw [ite_eq_left hsub]
    refine ⟨0, by simp [Float.toRat?, classify_zero, finiteToRat_zero], ?_⟩
    -- The flushed value is subnormal: `|q| < 2^fracBits · 2^(emin - fracBits) = 2^emin`.
    obtain ⟨-, -, hnorm⟩ := classify_finite_range hc
    have he : e = FloatFmt.f128.emin - FloatFmt.f128.fracBits := by
      rcases hnorm with h | h
      · omega
      · exact h
    have hmag : finiteToRat false m e < (2 : Rat) ^ FloatFmt.f128.emin := by
      rw [finiteToRat_false_eq_zpow, he]
      have hlt : (m : Rat) < ((2 ^ FloatFmt.f128.fracBits : Nat) : Rat) :=
        Rat.natCast_lt_natCast.mpr hsub.2
      have h2 : ((2 ^ FloatFmt.f128.fracBits : Nat) : Rat) * (2 : Rat) ^
          (FloatFmt.f128.emin - FloatFmt.f128.fracBits) = (2 : Rat) ^ FloatFmt.f128.emin := by
        push_cast
        rw [← Rat.zpow_natCast, ← Rat.zpow_add (by decide)]
        congr 1
      rw [← h2]
      exact Rat.mul_lt_mul_of_pos_right hlt (two_zpow_pos _)
    have h0 := finiteToRat_nonneg m e
    cases s
    · constructor <;> grind
    · rw [finiteToRat_true_eq] at e1 e2
      constructor <;> grind
  · rw [ite_eq_right hsub]
    exact ⟨_, hq, by grind, by grind⟩

end Zig
