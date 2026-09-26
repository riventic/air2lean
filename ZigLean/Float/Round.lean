import ZigLean.Float.Value

/-!
# Rounding

`Float.roundRat`: round an exact rational value to a float, to nearest, ties to even.
Every arithmetic op computes its exact result as a `Rat` and rounds it once through this
function (`docs/floats.md` §Semantics).
-/

namespace Zig

/-- Shift-form comparison lemmas for `ilog2`/`ilog2_spec`: `n <<< (-e).toNat < d <<< e.toNat`
encodes `n / d < 2 ^ e` for arbitrary `e : Int` (positive `e` shifts `d`, negative `e` shifts
`n`), entirely in `Nat`/`Int` — no `zpow`. -/
private theorem up_bound {n d la lb : Nat} (ha2 : n < 2 ^ (la + 1)) (hb1 : 2 ^ lb ≤ d) :
    n <<< (-(((la : Int) - (lb : Int)) + 1)).toNat < d <<< (((la : Int) - (lb : Int)) + 1).toNat := by
  simp only [Nat.shiftLeft_eq]
  rcases Nat.lt_or_ge la lb with hab | hab
  · have e1 : (((la : Int) - (lb : Int)) + 1).toNat = 0 := by omega
    have e2 : (-(((la : Int) - (lb : Int)) + 1)).toNat = lb - la - 1 := by omega
    rw [e1, e2]
    have hexp : (la + 1) + (lb - la - 1) = lb := by omega
    calc n * 2 ^ (lb - la - 1) < 2 ^ (la + 1) * 2 ^ (lb - la - 1) :=
          Nat.mul_lt_mul_of_lt_of_le ha2 (Nat.le_refl _) (Nat.pow_pos (by omega))
      _ = 2 ^ lb := by rw [← Nat.pow_add, hexp]
      _ ≤ d := hb1
      _ = d * 2 ^ 0 := by simp
  · have e1 : (((la : Int) - (lb : Int)) + 1).toNat = la - lb + 1 := by omega
    have e2 : (-(((la : Int) - (lb : Int)) + 1)).toNat = 0 := by omega
    rw [e1, e2]
    have hexp : lb + (la - lb + 1) = la + 1 := by omega
    calc n * 2 ^ 0 = n := by simp
      _ < 2 ^ (la + 1) := ha2
      _ = 2 ^ lb * 2 ^ (la - lb + 1) := by rw [← Nat.pow_add, hexp]
      _ ≤ d * 2 ^ (la - lb + 1) := Nat.mul_le_mul hb1 (Nat.le_refl _)

private theorem low_bound {n d la lb : Nat} (ha1 : 2 ^ la ≤ n) (hb2 : d < 2 ^ (lb + 1)) :
    d <<< (((la : Int) - (lb : Int)) - 1).toNat ≤ n <<< (-(((la : Int) - (lb : Int)) - 1)).toNat := by
  simp only [Nat.shiftLeft_eq]
  rcases Nat.lt_or_ge lb la with hab | hab
  · have e1 : (((la : Int) - (lb : Int)) - 1).toNat = la - lb - 1 := by omega
    have e2 : (-(((la : Int) - (lb : Int)) - 1)).toNat = 0 := by omega
    rw [e1, e2]
    have hexp : (lb + 1) + (la - lb - 1) = la := by omega
    calc d * 2 ^ (la - lb - 1) ≤ 2 ^ (lb + 1) * 2 ^ (la - lb - 1) :=
          Nat.le_of_lt (Nat.mul_lt_mul_of_lt_of_le hb2 (Nat.le_refl _) (Nat.pow_pos (by omega)))
      _ = 2 ^ la := by rw [← Nat.pow_add, hexp]
      _ ≤ n * 2 ^ 0 := by simp [ha1]
  · have e1 : (((la : Int) - (lb : Int)) - 1).toNat = 0 := by omega
    have e2 : (-(((la : Int) - (lb : Int)) - 1)).toNat = lb - la + 1 := by omega
    rw [e1, e2]
    have hexp : la + (lb - la + 1) = lb + 1 := by omega
    calc d * 2 ^ 0 = d := by simp
      _ ≤ 2 ^ (lb + 1) := Nat.le_of_lt hb2
      _ = 2 ^ la * 2 ^ (lb - la + 1) := by rw [← Nat.pow_add, hexp]
      _ ≤ n * 2 ^ (lb - la + 1) := Nat.mul_le_mul ha1 (Nat.le_refl _)

private theorem shiftLt_of_nonneg {n d : Nat} {e : Int} (he : 0 ≤ e)
    (h : n <<< (-e).toNat < d <<< e.toNat) : n < d * 2 ^ e.toNat := by
  have h0 : (-e).toNat = 0 := by omega
  rw [h0] at h; simpa [Nat.shiftLeft_eq] using h

private theorem shiftLt_of_nonpos {n d : Nat} {e : Int} (he : e ≤ 0)
    (h : n <<< (-e).toNat < d <<< e.toNat) : n * 2 ^ (-e).toNat < d := by
  have h0 : e.toNat = 0 := by omega
  rw [h0] at h; simpa [Nat.shiftLeft_eq] using h

private theorem shiftLe_of_nonneg {n d : Nat} {e : Int} (he : 0 ≤ e)
    (h : d <<< e.toNat ≤ n <<< (-e).toNat) : d * 2 ^ e.toNat ≤ n := by
  have h0 : (-e).toNat = 0 := by omega
  rw [h0] at h; simpa [Nat.shiftLeft_eq] using h

private theorem shiftLe_of_nonpos {n d : Nat} {e : Int} (he : e ≤ 0)
    (h : d <<< e.toNat ≤ n <<< (-e).toNat) : d ≤ n * 2 ^ (-e).toNat := by
  have h0 : e.toNat = 0 := by omega
  rw [h0] at h; simpa [Nat.shiftLeft_eq] using h

/-- Converse of `shiftLt_of_nonneg`/`shiftLt_of_nonpos`: build the shift-form comparison from
the concrete one, given the sign of `e` matching. -/
private theorem shiftLt_of_nonneg' {n d : Nat} {e : Int} (he : 0 ≤ e)
    (h : n < d * 2 ^ e.toNat) : n <<< (-e).toNat < d <<< e.toNat := by
  have h0 : (-e).toNat = 0 := by omega
  rw [h0]; simpa [Nat.shiftLeft_eq] using h

private theorem shiftLt_of_nonpos' {n d : Nat} {e : Int} (he : e ≤ 0)
    (h : n * 2 ^ (-e).toNat < d) : n <<< (-e).toNat < d <<< e.toNat := by
  have h0 : e.toNat = 0 := by omega
  rw [h0]; simpa [Nat.shiftLeft_eq] using h

/-- The shift-form comparison (`n / d < 2 ^ e`, see `up_bound`) is monotone in `e`: raising the
threshold keeps a true "less than". Used to widen `ilog2 n d`'s successor bound up to `e0 + prec`
for `roundRat`'s clamped exponent `e0`. -/
private theorem shiftLt_mono {n d : Nat} {e1 e2 : Int} (hle : e1 ≤ e2)
    (h : n <<< (-e1).toNat < d <<< e1.toNat) : n <<< (-e2).toNat < d <<< e2.toNat := by
  by_cases he1 : 0 ≤ e1
  · have he2 : 0 ≤ e2 := by omega
    have hc : n < d * 2 ^ e1.toNat := shiftLt_of_nonneg he1 h
    apply shiftLt_of_nonneg' he2
    have hmono : (2:Nat) ^ e1.toNat ≤ 2 ^ e2.toNat := Nat.pow_le_pow_right (by omega) (by omega)
    calc n < d * 2 ^ e1.toNat := hc
      _ ≤ d * 2 ^ e2.toNat := Nat.mul_le_mul_left d hmono
  · have he1' : e1 ≤ 0 := by omega
    by_cases he2 : 0 ≤ e2
    · have hc : n * 2 ^ (-e1).toNat < d := shiftLt_of_nonpos he1' h
      apply shiftLt_of_nonneg' he2
      have hp : 0 < 2 ^ (-e1).toNat := Nat.two_pow_pos _
      have hp2 : 0 < 2 ^ e2.toNat := Nat.two_pow_pos _
      calc n ≤ n * 2 ^ (-e1).toNat := Nat.le_mul_of_pos_right n hp
        _ < d := hc
        _ ≤ d * 2 ^ e2.toNat := Nat.le_mul_of_pos_right d hp2
    · have he2' : e2 ≤ 0 := by omega
      have hc : n * 2 ^ (-e1).toNat < d := shiftLt_of_nonpos he1' h
      apply shiftLt_of_nonpos' he2'
      have hmono : (2:Nat) ^ (-e2).toNat ≤ 2 ^ (-e1).toNat := Nat.pow_le_pow_right (by omega) (by omega)
      calc n * 2 ^ (-e2).toNat ≤ n * 2 ^ (-e1).toNat := Nat.mul_le_mul_left n hmono
        _ < d := hc

/-- `⌊log₂(n/d)⌋` for `n d : Nat`, both positive: a `Nat.log2` guess, corrected by one
comparison (`ilog2_spec`) — all in `Nat`/`Int`, so no `zpow` (`Rat^Int`) monotonicity is
ever needed, unlike the `Rat`-based `floorLog2` this replaces. -/
def ilog2 (n d : Nat) : Int :=
  let g : Int := (Nat.log2 n : Int) - (Nat.log2 d : Int)
  if n <<< (-g).toNat < d <<< g.toNat then g - 1 else g

/-- `ilog2 n d` is the floor of `log₂(n/d)`, stated without division or `zpow`: for a
nonnegative result `k`, `d * 2^k ≤ n < d * 2^(k+1)`; for a negative result `k`,
`d ≤ n * 2^(-k) < 2 * d`. -/
theorem ilog2_spec {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    (0 ≤ ilog2 n d → d * 2 ^ (ilog2 n d).toNat ≤ n ∧ n < d * 2 ^ (ilog2 n d + 1).toNat) ∧
    (ilog2 n d < 0 → d ≤ n * 2 ^ (-ilog2 n d).toNat ∧ n * 2 ^ (-ilog2 n d).toNat < 2 * d) := by
  have hn0 : n ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  have ha1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn0
  have ha2 : n < 2 ^ (n.log2 + 1) := (Nat.log2_lt hn0).mp (Nat.lt_succ_self _)
  have hb1 : 2 ^ d.log2 ≤ d := Nat.log2_self_le hd0
  have hb2 : d < 2 ^ (d.log2 + 1) := (Nat.log2_lt hd0).mp (Nat.lt_succ_self _)
  have hup := up_bound (la := n.log2) (lb := d.log2) ha2 hb1
  have hlow := low_bound (la := n.log2) (lb := d.log2) ha1 hb2
  simp only [ilog2]
  split
  next hcond =>
    refine ⟨fun hge => ⟨?_, ?_⟩, fun hlt => ⟨?_, ?_⟩⟩
    · exact shiftLe_of_nonneg hge hlow
    · have hgg : ((n.log2 : Int) - (d.log2 : Int) - 1) + 1 = (n.log2 : Int) - (d.log2 : Int) := by
        omega
      rw [hgg]
      exact shiftLt_of_nonneg (by omega) hcond
    · exact shiftLe_of_nonpos (by omega) hlow
    · have hstep := shiftLt_of_nonpos (e := (n.log2 : Int) - (d.log2 : Int)) (by omega) hcond
      have hexp : (-(((n.log2 : Int) - (d.log2 : Int)) - 1)).toNat
          = (-((n.log2 : Int) - (d.log2 : Int))).toNat + 1 := by omega
      rw [hexp, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2 d]
      exact (Nat.mul_lt_mul_right (by omega)).mpr hstep
  next hcond =>
    have hcond' := Nat.not_lt.mp hcond
    refine ⟨fun hge => ⟨?_, ?_⟩, fun hlt => ⟨?_, ?_⟩⟩
    · exact shiftLe_of_nonneg hge hcond'
    · exact shiftLt_of_nonneg (by omega) hup
    · exact shiftLe_of_nonpos (by omega) hcond'
    · have hstep := shiftLt_of_nonpos
          (e := ((n.log2 : Int) - (d.log2 : Int)) + 1) (by omega) hup
      have hexp : (-((n.log2 : Int) - (d.log2 : Int))).toNat
          = (-(((n.log2 : Int) - (d.log2 : Int)) + 1)).toNat + 1 := by omega
      rw [hexp, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2 d]
      exact (Nat.mul_lt_mul_right (by omega)).mpr hstep

/-- The shift-form fact one exponent step above `ilog2 n d`: `n / d < 2 ^ (ilog2 n d + 1)`, in
`up_bound`/`low_bound`'s shift encoding. Directly from `ilog2_spec`'s two branches (`.1` gives it
outright; `.2` gives the doubled form at `-ilog2 n d`, halved back down here). The base case
`shiftLt_mono` widens to reach `roundRat`'s clamped `e0 + prec`. -/
theorem ilog2_succ_bound {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    n <<< (-(ilog2 n d + 1)).toNat < d <<< (ilog2 n d + 1).toNat := by
  have hspec := ilog2_spec hn hd
  by_cases hk : 0 ≤ ilog2 n d
  · exact shiftLt_of_nonneg' (by omega) (hspec.1 hk).2
  · have hk' : ilog2 n d < 0 := by omega
    have h2 := (hspec.2 hk').2
    apply shiftLt_of_nonpos' (e := ilog2 n d + 1) (by omega)
    have heq : (-(ilog2 n d + 1)).toNat + 1 = (-ilog2 n d).toNat := by omega
    have hpoweq : (2:Nat) ^ (-ilog2 n d).toNat = 2 ^ (-(ilog2 n d + 1)).toNat * 2 := by
      rw [← heq, Nat.pow_succ]
    rw [hpoweq, ← Nat.mul_assoc] at h2
    omega

/-- Round-half-to-even of the (unreduced) fraction `N / D`, `D > 0`. -/
def roundQuot (N D : Nat) : Int :=
  let m := N / D
  let r := N % D
  if 2 * r < D then (m : Int)
  else if D < 2 * r then (m : Int) + 1
  else if m % 2 = 0 then (m : Int) else (m : Int) + 1

/-- `roundQuot` never overshoots `2 ^ prec` given `N / D < 2 ^ prec` (`D > 0` implicit: `D = 0`
gives `N / D = 0` and the bound holds trivially). Ties round up to `m + 1`, which reaches
`2 ^ prec` only at the boundary `N / D = 2 ^ prec - 1` — the carry-out case `finalizeRounded_spec`
already allows via `m0 ≤ 2 ^ fmt.prec`. -/
private theorem roundQuot_le {N D : Nat} (prec : Nat) (h : N < D * 2 ^ prec) :
    roundQuot N D ≤ (2:Int) ^ prec := by
  have hm : N / D < 2 ^ prec := Nat.div_lt_of_lt_mul (Nat.mul_comm D (2 ^ prec) ▸ h)
  have hcast : ((2 ^ prec : Nat) : Int) = (2:Int) ^ prec := by exact_mod_cast rfl
  unfold roundQuot
  simp only []
  split
  · omega
  · split
    · omega
    · split <;> omega

private theorem expBits_le_width_pred (fmt : FloatFmt) : fmt.expBits ≤ fmt.width - 1 := by
  cases fmt <;> decide

private theorem width_pos (fmt : FloatFmt) : 1 ≤ fmt.width := by
  cases fmt <;> decide

/-- Bit-level content of `Float.pack`: the packed value stays in range, its top bit is the
sign, the exponent field is recovered exactly by shifting past the low
`fmt.width - 1 - fmt.expBits` bits, and those low bits are exactly `rest`. -/
theorem pack_bits_spec (fmt : FloatFmt) (sign : Bool) {exp rest : Nat}
    (hexp : exp < 2 ^ fmt.expBits) (hrest : rest < 2 ^ (fmt.width - 1 - fmt.expBits)) :
    (Float.pack fmt sign exp rest).bits.toNat < 2 ^ fmt.width ∧
    (Float.pack fmt sign exp rest).bits.msb = sign ∧
    ((Float.pack fmt sign exp rest).bits.toNat >>> (fmt.width - 1 - fmt.expBits)) % 2 ^ fmt.expBits
      = exp ∧
    (Float.pack fmt sign exp rest).bits.toNat % 2 ^ (fmt.width - 1 - fmt.expBits) = rest := by
  have hER : fmt.expBits + (fmt.width - 1 - fmt.expBits) = fmt.width - 1 := by
    have := expBits_le_width_pred fmt; omega
  have h1 : exp <<< (fmt.width - 1 - fmt.expBits) ||| rest
      = exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hrest exp, Nat.shiftLeft_eq]
  have hb : exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest < 2 ^ (fmt.width - 1) := by
    have hstep : exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest
        < (exp + 1) * 2 ^ (fmt.width - 1 - fmt.expBits) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hstep2 : (exp + 1) * 2 ^ (fmt.width - 1 - fmt.expBits)
        ≤ 2 ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits) := Nat.mul_le_mul_right _ hexp
    have hlt : exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest
        < 2 ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits) := Nat.lt_of_lt_of_le hstep hstep2
    rwa [← Nat.pow_add, hER] at hlt
  have hvraw : (Float.pack fmt sign exp rest).bits.toNat
      = ((if sign then 1 else 0 : Nat) <<< (fmt.width - 1) |||
          exp <<< (fmt.width - 1 - fmt.expBits) ||| rest) % 2 ^ fmt.width := by
    unfold Float.pack; rw [BitVec.toNat_ofNat]
  have hmsb : (Float.pack fmt sign exp rest).bits.msb
      = decide (2 ^ (fmt.width - 1) ≤ (Float.pack fmt sign exp rest).bits.toNat) :=
    BitVec.msb_eq_decide _
  cases sign with
  | false =>
    have hveq : (Float.pack fmt false exp rest).bits.toNat
        = exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest := by
      rw [hvraw]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_shiftLeft, Nat.zero_or, h1]
      have h2pow : (2:Nat) ^ (fmt.width - 1) ≤ 2 ^ fmt.width :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hmsb, hveq]; simp only [decide_eq_false_iff_not]; omega
    · rw [hveq, Nat.shiftRight_eq_div_pow, Nat.mul_comm exp (2 ^ (fmt.width - 1 - fmt.expBits)),
        Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hrest, Nat.add_zero,
        Nat.mod_eq_of_lt hexp]
    · rw [hveq, Nat.mul_comm exp (2 ^ (fmt.width - 1 - fmt.expBits)), Nat.mul_add_mod,
        Nat.mod_eq_of_lt hrest]
  | true =>
    have hb' : exp <<< (fmt.width - 1 - fmt.expBits) ||| rest < 2 ^ (fmt.width - 1) := by
      rw [h1]; exact hb
    have hassoc : (if true then 1 else 0 : Nat) <<< (fmt.width - 1) |||
        exp <<< (fmt.width - 1 - fmt.expBits) ||| rest
        = 1 <<< (fmt.width - 1) ||| (exp <<< (fmt.width - 1 - fmt.expBits) ||| rest) := by
      simp only [ite_true]; rw [Nat.or_assoc]
    have hone : (1 : Nat) <<< (fmt.width - 1) ||| (exp <<< (fmt.width - 1 - fmt.expBits) ||| rest)
        = 1 <<< (fmt.width - 1) + (exp <<< (fmt.width - 1 - fmt.expBits) ||| rest) :=
      (Nat.shiftLeft_add_eq_or_of_lt hb' 1).symm
    have heq : (2:Nat) ^ (fmt.width - 1) = 2 ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits) := by
      rw [← Nat.pow_add, hER]
    have hveq : (Float.pack fmt true exp rest).bits.toNat
        = 2 ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits)
          + (exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest) := by
      rw [hvraw, hassoc, hone, h1, Nat.one_shiftLeft, heq]
      have hw1 := width_pos fmt
      have h2pow : (2:Nat) * (2 ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits)) = 2 ^ fmt.width := by
        rw [← heq]
        have hsucc : (2:Nat) * 2 ^ (fmt.width - 1) = 2 ^ fmt.width := by
          rw [← Nat.pow_succ']; congr 1; omega
        exact hsucc
      exact Nat.mod_eq_of_lt (by omega)
    have hE2 : (2:Nat) ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits)
        + (exp * 2 ^ (fmt.width - 1 - fmt.expBits) + rest)
        = (2 ^ fmt.expBits + exp) * 2 ^ (fmt.width - 1 - fmt.expBits) + rest := by
      rw [Nat.add_mul]; omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hmsb, hveq]; simp only [decide_eq_true_eq]; omega
    · rw [hveq, hE2, Nat.shiftRight_eq_div_pow,
        Nat.mul_comm (2 ^ fmt.expBits + exp) (2 ^ (fmt.width - 1 - fmt.expBits)),
        Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hrest, Nat.add_zero,
        Nat.add_mod_left, Nat.mod_eq_of_lt hexp]
    · rw [hveq, hE2, Nat.mul_comm (2 ^ fmt.expBits + exp) (2 ^ (fmt.width - 1 - fmt.expBits)),
        Nat.mul_add_mod, Nat.mod_eq_of_lt hrest]

theorem restW_eq_fracBits (fmt : FloatFmt) (h : fmt ≠ .f80) :
    fmt.width - 1 - fmt.expBits = fmt.fracBits := by
  cases fmt <;> first | exact absurd rfl h | decide

theorem restW_eq_fracBits_succ_f80 :
    FloatFmt.f80.width - 1 - FloatFmt.f80.expBits = FloatFmt.f80.fracBits + 1 := by decide

theorem expMask_succ (fmt : FloatFmt) : 2 ^ fmt.expBits - 1 + 1 = 2 ^ fmt.expBits := by
  have := Nat.two_pow_pos fmt.expBits; omega

/-- The biased-exponent field `encodeFinite` computes stays strictly below the all-ones pattern,
given the caller's overflow check (`he_hi`) already ruled out `finalizeRounded`'s `Float.inf`
branch. Shared by every non-zero case, both `f80` and not; strong enough to give both `≠ expMask`
(so `classify` doesn't take the nan/inf branch) and `< 2 ^ expBits` (so `pack_bits_spec` applies). -/
theorem fieldExp_lt (fmt : FloatFmt) (e : Int)
    (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    (e + (fmt.bias : Int) + (fmt.fracBits : Int)).toNat < 2 ^ fmt.expBits - 1 := by
  have hEB1 : 1 ≤ fmt.expBits := by cases fmt <;> decide
  obtain ⟨k, hk⟩ : ∃ k, fmt.expBits = k + 1 := ⟨fmt.expBits - 1, by omega⟩
  have hpow : (2 : Nat) ^ fmt.expBits = 2 * 2 ^ k := by rw [hk, Nat.pow_succ']
  have hbias : fmt.bias = 2 ^ k - 1 := by
    unfold FloatFmt.bias
    rw [hk, Nat.add_sub_cancel]
  have he_hi' := he_hi
  simp only [FloatFmt.emax, FloatFmt.prec] at he_hi'
  rw [hbias] at he_hi' ⊢
  have hp1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- Encode an already-rounded magnitude `m * 2^e` (`m < 2 ^ fmt.prec`, `e` in range).
`m = 0` is a zero; `m < 2 ^ fmt.fracBits` is subnormal. For `f80`, `m` already carries the
explicit integer bit (it is `2 ^ fmt.fracBits + fraction` in the normal case), so the low
`fmt.width - 1 - fmt.expBits` bits are `m` itself in both cases. -/
def Float.encodeFinite (fmt : FloatFmt) (neg : Bool) (m : Nat) (e : Int) : Float fmt :=
  if m = 0 then Float.zero neg
  else if m < 2 ^ fmt.fracBits then
    Float.pack fmt neg 0 m
  else
    let fieldExp := (e + fmt.bias + fmt.fracBits).toNat
    let rest : Nat := match fmt with
      | .f80 => m
      | _ => m - 2 ^ fmt.fracBits
    Float.pack fmt neg fieldExp rest

/-- `Float.encodeFinite`'s result is never NaN and carries the given sign, given the rounded
magnitude fits `fmt.prec` bits and the biased exponent does not overflow (`finalizeRounded`'s
own overflow check, restated here). -/
private theorem encodeFinite_spec (fmt : FloatFmt) (neg : Bool) (m : Nat) (e : Int)
    (hm : m < 2 ^ fmt.prec) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    (Float.encodeFinite fmt neg m e).isNaN = false ∧
    (Float.encodeFinite fmt neg m e).signBit = neg := by
  unfold Float.encodeFinite
  split
  · exact ⟨by cases fmt <;> cases neg <;> decide, by cases fmt <;> cases neg <;> decide⟩
  · rename_i hm0
    split
    · rename_i hmfrac
      by_cases hf80 : fmt = .f80
      · subst hf80
        have hrest : m < 2 ^ (FloatFmt.f80.width - 1 - FloatFmt.f80.expBits) := by
          rw [restW_eq_fracBits_succ_f80]; omega
        obtain ⟨_, hmsb, hexpEq, hrestEq⟩ :=
          pack_bits_spec .f80 neg (exp := 0) (by decide) hrest
        rw [restW_eq_fracBits_succ_f80] at hexpEq hrestEq
        refine ⟨?_, hmsb⟩
        unfold Float.isNaN
        simp only [Float.classify]
        rw [expMask_succ]
        have hintBit : (Float.pack .f80 neg 0 m).bits.toNat >>> FloatFmt.f80.fracBits % 2 = 0 := by
          rw [show FloatFmt.f80.fracBits = 63 from rfl] at hrestEq hmfrac ⊢
          simp only [Nat.shiftRight_eq_div_pow] at hrestEq ⊢
          omega
        rw [ite_eq_right (by rw [hexpEq]; decide), ite_eq_left hintBit, ite_eq_left hexpEq]
      · have hrestBound : fmt.fracBits ≤ fmt.width - 1 - fmt.expBits := by
          cases fmt <;> first | exact absurd rfl hf80 | decide
        have hrest : m < 2 ^ (fmt.width - 1 - fmt.expBits) :=
          Nat.lt_of_lt_of_le hmfrac (Nat.pow_le_pow_right (by omega) hrestBound)
        obtain ⟨_, hmsb, hexpEq, _⟩ := pack_bits_spec fmt neg (Nat.two_pow_pos fmt.expBits) hrest
        rw [restW_eq_fracBits fmt hf80] at hexpEq
        refine ⟨?_, hmsb⟩
        unfold Float.isNaN
        cases fmt with
        | f80 => exact absurd rfl hf80
        | f16 | f32 | f64 | f128 =>
          simp only [Float.classify]
          rw [expMask_succ]
          rw [ite_eq_right (by rw [hexpEq]; decide), ite_eq_left hexpEq]
    · rename_i hmfrac
      by_cases hf80 : fmt = .f80
      · subst hf80
        generalize hfieldExp :
          (e + (FloatFmt.f80.bias : Int) + (FloatFmt.f80.fracBits : Int)).toNat = fieldExp
        have hrest : m < 2 ^ (FloatFmt.f80.width - 1 - FloatFmt.f80.expBits) := by
          rw [restW_eq_fracBits_succ_f80, show FloatFmt.f80.fracBits = 63 from rfl]
          rw [show FloatFmt.f80.prec = 64 from rfl] at hm; exact hm
        have hbound : fieldExp < 2 ^ FloatFmt.f80.expBits - 1 := by
          rw [← hfieldExp]; exact fieldExp_lt .f80 e he_hi
        have hne : fieldExp ≠ 2 ^ FloatFmt.f80.expBits - 1 := by omega
        have hexp : fieldExp < 2 ^ FloatFmt.f80.expBits := by omega
        obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec .f80 neg hexp hrest
        rw [restW_eq_fracBits_succ_f80] at hexpEq hrestEq
        have hintBit :
            (Float.pack .f80 neg fieldExp m).bits.toNat >>> FloatFmt.f80.fracBits % 2 = 1 := by
          rw [show FloatFmt.f80.fracBits = 63 from rfl] at hrestEq ⊢
          simp only [Nat.shiftRight_eq_div_pow] at hrestEq ⊢
          rw [show FloatFmt.f80.prec = 64 from rfl] at hm
          rw [show FloatFmt.f80.fracBits = 63 from rfl] at hmfrac
          omega
        refine ⟨?_, hmsb⟩
        unfold Float.isNaN
        simp only [Float.classify]
        rw [expMask_succ]
        rw [ite_eq_right (by rw [hexpEq]; exact hne), ite_eq_right (by omega), hexpEq]
        by_cases hz : fieldExp = 0
        · rw [ite_eq_left hz]
        · rw [ite_eq_right hz]
      · simp only []
        generalize hfieldExp : (e + (fmt.bias : Int) + (fmt.fracBits : Int)).toNat = fieldExp
        have hrestBound : fmt.fracBits ≤ fmt.width - 1 - fmt.expBits := by
          cases fmt <;> first | exact absurd rfl hf80 | decide
        have hrest : m - 2 ^ fmt.fracBits < 2 ^ (fmt.width - 1 - fmt.expBits) := by
          have h1 : m - 2 ^ fmt.fracBits < 2 ^ fmt.fracBits := by
            have hp : fmt.prec = fmt.fracBits + 1 := rfl
            have h2 : (2 : Nat) ^ fmt.prec = 2 * 2 ^ fmt.fracBits := by rw [hp, Nat.pow_succ']
            omega
          exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hrestBound)
        have hbound : fieldExp < 2 ^ fmt.expBits - 1 := by
          rw [← hfieldExp]; exact fieldExp_lt fmt e he_hi
        have hne : fieldExp ≠ 2 ^ fmt.expBits - 1 := by omega
        have hexp : fieldExp < 2 ^ fmt.expBits := by omega
        obtain ⟨_, hmsb, hexpEq, _⟩ := pack_bits_spec fmt neg hexp hrest
        rw [restW_eq_fracBits fmt hf80] at hexpEq
        refine ⟨?_, hmsb⟩
        unfold Float.isNaN
        cases fmt with
        | f80 => exact absurd rfl hf80
        | f16 | f32 | f64 | f128 =>
          simp only [Float.classify]
          rw [expMask_succ]
          rw [ite_eq_right (by rw [hexpEq]; exact hne), hexpEq]
          by_cases hz : fieldExp = 0
          · rw [ite_eq_left hz]
          · rw [ite_eq_right hz]

/-- Shared tail of every "I already have a correctly-rounded-to-nearest-even mantissa `m0` at
exponent `e0`" computation (`roundRat`, and `Float.sqrt` in `Ops.lean`, which rounds via exact
integer square root instead of `roundTiesEven`). `m0` may carry out to `2 ^ fmt.prec`
(renormalized here); `e0` may put the result out of range (→ `inf`). -/
def Float.finalizeRounded (fmt : FloatFmt) (neg : Bool) (m0 : Int) (e0 : Int) : Float fmt :=
  let (m, e) : Nat × Int :=
    if m0 = (2 : Int) ^ fmt.prec then (2 ^ (fmt.prec - 1), e0 + 1) else (m0.toNat, e0)
  if e + (fmt.prec - 1 : Int) > fmt.emax then Float.inf neg else Float.encodeFinite fmt neg m e

/-- `Float.finalizeRounded`'s result is never NaN and carries the given sign, given the
pre-renormalization mantissa fits `2 ^ fmt.prec` (`m0 = 2 ^ fmt.prec` is the carry-out case,
renormalized to `2 ^ (fmt.prec - 1)` at `e0 + 1`). No hypothesis on `e0`: either overflow check
outcome keeps the sign and rules out NaN, via `Float.inf` or `encodeFinite_spec`. Public: shared
with `Float.sqrt`'s nonneg proof (`Lemmas.lean`). -/
theorem finalizeRounded_spec (fmt : FloatFmt) (neg : Bool) (m0 e0 : Int)
    (hm0 : m0 ≤ 2 ^ fmt.prec) :
    (Float.finalizeRounded fmt neg m0 e0).isNaN = false ∧
    (Float.finalizeRounded fmt neg m0 e0).signBit = neg := by
  have hcast : ((2 : Nat) ^ fmt.prec : Int) = (2 : Int) ^ fmt.prec := by exact_mod_cast rfl
  unfold Float.finalizeRounded
  split
  rename_i x m e heq
  by_cases hEq : m0 = (2 : Int) ^ fmt.prec
  · rw [ite_eq_left hEq] at heq
    injection heq with hm he
    subst hm; subst he
    split
    · exact ⟨by cases fmt <;> cases neg <;> decide, by cases fmt <;> cases neg <;> decide⟩
    · rename_i hoverflow
      apply encodeFinite_spec
      · have hp1 : 1 ≤ fmt.prec := by cases fmt <;> decide
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      · omega
  · rw [ite_eq_right hEq] at heq
    injection heq with hm he
    subst hm; subst he
    split
    · exact ⟨by cases fmt <;> cases neg <;> decide, by cases fmt <;> cases neg <;> decide⟩
    · rename_i hoverflow
      apply encodeFinite_spec
      · have := Nat.two_pow_pos fmt.prec
        rw [← hcast] at hm0 hEq; omega
      · omega

/-- `roundRat`'s quotient `N / D` stays below `2 ^ prec`, given the
clamp `e0 ≥ ilog2 n d - (prec - 1)` (always true of `roundRat`'s `e0`, a `Max.max` against a
floor). Widens `ilog2_succ_bound` up to `e0 + prec` via `shiftLt_mono`, splits on `e0`'s sign to
match `N`/`D`'s own split. -/
theorem roundRat_N_lt {n d : Nat} (hn : 0 < n) (hd : 0 < d) (prec : Nat) (e0 : Int)
    (he0 : ilog2 n d - ((prec : Int) - 1) ≤ e0) :
    (if e0 ≥ 0 then n else n <<< (-e0).toNat)
      < (if e0 ≥ 0 then d <<< e0.toNat else d) * 2 ^ prec := by
  have hmono : n <<< (-(e0 + (prec:Int))).toNat < d <<< (e0 + (prec:Int)).toNat :=
    shiftLt_mono (by omega) (ilog2_succ_bound hn hd)
  split
  · rename_i he0'
    have hc : n < d * 2 ^ (e0 + (prec:Int)).toNat := shiftLt_of_nonneg (by omega) hmono
    rw [show (e0 + (prec:Int)).toNat = e0.toNat + prec from by omega, Nat.pow_add,
      ← Nat.mul_assoc] at hc
    rwa [Nat.shiftLeft_eq]
  · rename_i he0'
    have he0'' : e0 < 0 := by omega
    by_cases he' : 0 ≤ e0 + (prec:Int)
    · have hc : n < d * 2 ^ (e0 + (prec:Int)).toNat := shiftLt_of_nonneg he' hmono
      have hsplit : (e0 + (prec:Int)).toNat + (-e0).toNat = prec := by omega
      rw [Nat.shiftLeft_eq]
      calc n * 2 ^ (-e0).toNat < d * 2 ^ (e0 + (prec:Int)).toNat * 2 ^ (-e0).toNat :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hc
        _ = d * 2 ^ prec := by rw [Nat.mul_assoc, ← Nat.pow_add, hsplit]
    · have he'' : e0 + (prec:Int) ≤ 0 := by omega
      have hc : n * 2 ^ (-(e0 + (prec:Int))).toNat < d := shiftLt_of_nonpos he'' hmono
      have hsplit : (-(e0 + (prec:Int))).toNat + prec = (-e0).toNat := by omega
      rw [Nat.shiftLeft_eq]
      calc n * 2 ^ (-e0).toNat = n * 2 ^ (-(e0 + (prec:Int))).toNat * 2 ^ prec := by
            rw [Nat.mul_assoc, ← Nat.pow_add, hsplit]
        _ < d * 2 ^ prec := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hc

/-- `roundRat`'s pre-renormalization mantissa `roundQuot N D` never exceeds `2 ^ prec`
(`roundRat_N_lt`, then `roundQuot_le`). -/
theorem roundRat_m0_le {n d : Nat} (hn : 0 < n) (hd : 0 < d) (prec : Nat) (e0 : Int)
    (he0 : ilog2 n d - ((prec : Int) - 1) ≤ e0) :
    roundQuot (if e0 ≥ 0 then n else n <<< (-e0).toNat)
        (if e0 ≥ 0 then d <<< e0.toNat else d) ≤ (2:Int) ^ prec :=
  roundQuot_le prec (roundRat_N_lt hn hd prec e0 he0)

/-- Round `|q|` to `fmt`, to nearest, ties to even; `neg` gives the sign, also of a zero
result. Subnormals and overflow (→ `inf`) follow from the exponent clamp and range check
in `finalizeRounded`; no case is special beyond them. Exact: works on `Rat`
numerator/denominator, never `Float`. -/
def Float.roundRat (fmt : FloatFmt) (neg : Bool) (q : Rat) : Float fmt :=
  let q := q.abs
  if q = 0 then Float.zero neg
  else
    let n := q.num.toNat
    let d := q.den
    let p : Int := fmt.prec
    -- `Max.max`: plain `max` would resolve to `Zig.max` (the `BitVec` one) in this namespace.
    let e0 := Max.max (ilog2 n d - (p - 1)) (fmt.emin - (p - 1))
    -- `N / D = (n / d) / 2 ^ e0`, as `Nat`s: shift `n` left when `e0 < 0`, `d` when `e0 ≥ 0`.
    let N := if e0 ≥ 0 then n else n <<< (-e0).toNat
    let D := if e0 ≥ 0 then d <<< e0.toNat else d
    let m0 := roundQuot N D
    Float.finalizeRounded fmt neg m0 e0

/-- A nonzero rounding result is never NaN and carries the caller's sign. The zero case
(`roundRat_zero` downstream in `Lemmas.lean`) needs no such spec: it reduces to `Float.zero neg`
directly. -/
theorem roundRat_ne_zero_spec (fmt : FloatFmt) (neg : Bool) {q : Rat} (hq : q ≠ 0) :
    (Float.roundRat fmt neg q).isNaN = false ∧ (Float.roundRat fmt neg q).signBit = neg := by
  have hden : q.abs.den = q.den := by
    unfold Rat.abs; split
    · rfl
    · exact Rat.neg_den q
  have hnum_nonneg : 0 ≤ q.abs.num := by
    unfold Rat.abs; split
    · next h => exact Rat.num_nonneg.mpr h
    · next h =>
      rw [Rat.neg_num]
      have hn : ¬ 0 ≤ q.num := fun hpos => h (Rat.num_nonneg.mp hpos)
      omega
  have hnum_ne : q.abs.num ≠ 0 := by
    intro hc
    apply hq
    apply Rat.num_eq_zero.mp
    unfold Rat.abs at hc
    split at hc
    · exact hc
    · rw [Rat.neg_num] at hc; omega
  have habs_ne : q.abs ≠ 0 := fun heq => hnum_ne (Rat.num_eq_zero.mpr heq)
  have hn : 0 < q.abs.num.toNat := by omega
  have hd : 0 < q.abs.den := hden ▸ q.den_pos
  unfold Float.roundRat
  rw [ite_eq_right habs_ne]
  simp only []
  apply finalizeRounded_spec
  apply roundRat_m0_le hn hd fmt.prec
  omega

end Zig
