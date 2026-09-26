import ZigLean.Float.Lemmas

/-!
# Round trip: decode ∘ encode

`classify ∘ encodeFinite` is the identity on in-range mantissa/exponent pairs
(`classify_encodeFinite`), and `roundRat` of an exactly representable value does no rounding
(`roundRat_finiteToRat`): it gives back the value (`roundRat_finiteToRat_toRat`), and for the
canonical pair of a float, the float itself (`roundRat_exact`). Consequences: signed-zero
arithmetic (`add_zero_right`, `mul_zero_right`), exact integer conversion (`ofInt_exact`). Last,
`roundRat_mono`: rounding is monotone on nonnegative values. The key facts: `ilog2` finds the
exact exponent, and `roundQuot` divides with remainder `0` (`roundQuot_mul_self`), so
`finalizeRounded` neither carries nor overflows.
-/

namespace Zig

/-- `classify` of a packed pattern, non-`f80`, with the exponent field below all-ones. -/
theorem classify_pack_of_ne_f80 {fmt : FloatFmt} (hf : fmt ≠ .f80) (s : Bool) {exp rest : Nat}
    (hexp : exp < 2 ^ fmt.expBits - 1) (hrest : rest < 2 ^ fmt.fracBits) :
    (Float.pack fmt s exp rest).classify =
      if exp = 0 then .finite s rest (fmt.emin - fmt.fracBits)
      else .finite s (2 ^ fmt.fracBits + rest) ((exp : Int) - fmt.bias - fmt.fracBits) := by
  have hrest' : rest < 2 ^ (fmt.width - 1 - fmt.expBits) := by rwa [restW_eq_fracBits fmt hf]
  obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec fmt s (exp := exp) (by omega) hrest'
  rw [restW_eq_fracBits fmt hf] at hexpEq hrestEq
  cases fmt with
  | f80 => exact absurd rfl hf
  | f16 | f32 | f64 | f128 =>
    simp only [Float.classify]
    rw [expMask_succ, hexpEq, hrestEq, hmsb, ite_eq_right (by omega)]

/-- `classify` of a packed `f80` pattern with the exponent field below all-ones and a valid
integer bit (set, or the exponent field zero). -/
theorem classify_pack_f80 (s : Bool) {exp rest : Nat}
    (hexp : exp < 2 ^ FloatFmt.f80.expBits - 1) (hrest : rest < 2 ^ FloatFmt.f80.prec)
    (hvalid : 2 ^ FloatFmt.f80.fracBits ≤ rest ∨ exp = 0) :
    (Float.pack .f80 s exp rest).classify =
      if exp = 0 then .finite s rest (FloatFmt.f80.emin - FloatFmt.f80.fracBits)
      else .finite s rest ((exp : Int) - FloatFmt.f80.bias - FloatFmt.f80.fracBits) := by
  have hrest' : rest < 2 ^ (FloatFmt.f80.width - 1 - FloatFmt.f80.expBits) := by
    rw [restW_eq_fracBits_succ_f80]; exact hrest
  obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec .f80 s (exp := exp) (by omega) hrest'
  rw [restW_eq_fracBits_succ_f80] at hexpEq hrestEq
  simp only [Float.classify]
  rw [expMask_succ, hexpEq, hmsb, ite_eq_right (by omega)]
  generalize (Float.pack .f80 s exp rest).bits.toNat = v at hrestEq ⊢
  simp only [show FloatFmt.f80.fracBits = 63 from rfl, show FloatFmt.f80.prec = 64 from rfl,
    Nat.shiftRight_eq_div_pow] at hrestEq hvalid hrest ⊢
  have hv63 : v % 2 ^ 63 = rest % 2 ^ 63 := by
    rw [← hrestEq, Nat.mod_mod_of_dvd _ (by decide)]
  have hib : v / 2 ^ 63 % 2 = rest / 2 ^ 63 := by
    have := Nat.mod_add_div v (2 ^ 64)
    omega
  rw [hib, hv63]
  by_cases hr : 2 ^ 63 ≤ rest
  · have h1 : rest / 2 ^ 63 = 1 := by omega
    have h2 : 2 ^ 63 + rest % 2 ^ 63 = rest := by omega
    simp only [h1, Nat.one_ne_zero, ↓reduceIte, h2]
  · have h0 : exp = 0 := by omega
    have h1 : rest / 2 ^ 63 = 0 := by omega
    subst h0
    simp only [h1, ↓reduceIte, Nat.mod_eq_of_lt (show rest < 2 ^ 63 by omega)]


/-- The biased field `encodeFinite` writes: `1 ≤ fieldExp < expMask` for a normal `e`. -/
private theorem fieldExp_bounds (fmt : FloatFmt) {e : Int}
    (he_lo : fmt.emin - fmt.fracBits ≤ e) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    1 ≤ (e + (fmt.bias : Int) + (fmt.fracBits : Int)).toNat ∧
    (e + (fmt.bias : Int) + (fmt.fracBits : Int)).toNat < 2 ^ fmt.expBits - 1 ∧
    ((e + (fmt.bias : Int) + (fmt.fracBits : Int)).toNat : Int) - fmt.bias - fmt.fracBits = e := by
  have h := fieldExp_lt fmt e he_hi
  simp only [FloatFmt.emin] at he_lo
  omega

/-- Decoding an `encodeFinite` result gives back its mantissa and exponent, for a nonzero
mantissa that fits `fmt.prec` bits and an exponent in range. A mantissa below `2 ^ fmt.fracBits`
(subnormal) must sit at the subnormal exponent `emin - fracBits`. -/
theorem classify_encodeFinite (fmt : FloatFmt) (s : Bool) {m : Nat} {e : Int}
    (hm0 : 0 < m) (hm : m < 2 ^ fmt.prec)
    (he_lo : fmt.emin - fmt.fracBits ≤ e) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax)
    (hnorm : 2 ^ fmt.fracBits ≤ m ∨ e = fmt.emin - fmt.fracBits) :
    (Float.encodeFinite fmt s m e).classify = .finite s m e := by
  have hp : (2 : Nat) ^ fmt.prec = 2 * 2 ^ fmt.fracBits := by
    rw [show fmt.prec = fmt.fracBits + 1 from rfl, Nat.pow_succ']
  obtain ⟨hf1, hf2, hf3⟩ := fieldExp_bounds fmt he_lo he_hi
  unfold Float.encodeFinite
  rw [ite_eq_right (by omega)]
  by_cases hsub : m < 2 ^ fmt.fracBits
  · rw [ite_eq_left hsub]
    have he : e = fmt.emin - fmt.fracBits := by omega
    subst he
    by_cases hf80 : fmt = .f80
    · subst hf80
      rw [classify_pack_f80 s (by decide) hm (Or.inr rfl)]; rfl
    · rw [classify_pack_of_ne_f80 hf80 s (by have := Nat.two_pow_pos fmt.expBits; cases fmt <;> first | exact absurd rfl hf80 | decide) hsub]
      rfl
  · rw [ite_eq_right hsub]
    by_cases hf80 : fmt = .f80
    · subst hf80
      simp only []
      rw [classify_pack_f80 s hf2 hm (Or.inl (by omega)), ite_eq_right (by omega), hf3]
    · have hrest : m - 2 ^ fmt.fracBits < 2 ^ fmt.fracBits := by omega
      have key := classify_pack_of_ne_f80 hf80 s hf2 hrest
      have hm' : 2 ^ fmt.fracBits + (m - 2 ^ fmt.fracBits) = m := by omega
      cases fmt with
      | f80 => exact absurd rfl hf80
      | f16 | f32 | f64 | f128 =>
        simp only []
        rw [key, ite_eq_right (by omega), hf3, hm']


/-- Scaling both sides by the same power of two: `A * 2^x ≤ B * 2^y` depends only on `x - y`. -/
theorem mul_pow_le_congr {A B x y x' y' : Nat} (h : (x : Int) - y = x' - y') :
    A * 2 ^ x ≤ B * 2 ^ y ↔ A * 2 ^ x' ≤ B * 2 ^ y' := by
  have key : ∀ a b c d : Nat, a + d = b + c → (A * 2 ^ a ≤ B * 2 ^ b → A * 2 ^ c ≤ B * 2 ^ d) := by
    intro a b c d habcd hle
    have h1 : A * 2 ^ c * 2 ^ b ≤ B * 2 ^ d * 2 ^ b :=
      calc A * 2 ^ c * 2 ^ b = A * 2 ^ a * 2 ^ d := by
            rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
        _ ≤ B * 2 ^ b * 2 ^ d := Nat.mul_le_mul_right _ hle
        _ = B * 2 ^ d * 2 ^ b := Nat.mul_right_comm _ _ _
    exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos _)
  exact ⟨key x y x' y' (by omega), key x' y' x y (by omega)⟩

/-- Strict form of `mul_pow_le_congr`. -/
theorem mul_pow_lt_congr {A B x y x' y' : Nat} (h : (x : Int) - y = x' - y') :
    A * 2 ^ x < B * 2 ^ y ↔ A * 2 ^ x' < B * 2 ^ y' := by
  have := (mul_pow_le_congr (A := B) (B := A) (x := y) (y := x) (x' := y') (y' := x') (by omega))
  constructor
  · intro hlt; exact Nat.lt_of_not_le fun hc => Nat.not_le_of_lt hlt (this.mpr hc)
  · intro hlt; exact Nat.lt_of_not_le fun hc => Nat.not_le_of_lt hlt (this.mp hc)

/-- Equality form of `mul_pow_le_congr`. -/
theorem mul_pow_eq_congr {A B x y x' y' : Nat} (h : (x : Int) - y = x' - y') :
    A * 2 ^ x = B * 2 ^ y ↔ A * 2 ^ x' = B * 2 ^ y' := by
  have h1 := mul_pow_le_congr (A := A) (B := B) h
  have h2 := mul_pow_le_congr (A := B) (B := A) (x := y) (y := x) (x' := y') (y' := x') (by omega)
  constructor
  · intro heq; exact Nat.le_antisymm (h1.mp (Nat.le_of_eq heq)) (h2.mp (Nat.le_of_eq heq.symm))
  · intro heq; exact Nat.le_antisymm (h1.mpr (Nat.le_of_eq heq)) (h2.mpr (Nat.le_of_eq heq.symm))

/-- The magnitude of a finite value, as a `mkRat` of naturals. -/
theorem finiteToRat_false_eq_mkRat (m : Nat) (e : Int) :
    finiteToRat false m e = mkRat ((m * 2 ^ e.toNat : Nat) : Int) (2 ^ (-e).toNat) := by
  rw [Rat.mkRat_eq_div]
  unfold finiteToRat
  simp only [Bool.false_eq_true, ↓reduceIte, Rat.intCast_natCast, Rat.natCast_mul,
    Rat.natCast_pow]
  split
  · rw [show (-e).toNat = 0 by omega, Rat.pow_zero]
    have h1 := Rat.mul_div_cancel (a := (m : Rat) * (2 : Rat) ^ e.toNat) (b := 1) (by decide)
    rw [Rat.mul_one] at h1
    exact h1.symm
  · rw [show e.toNat = 0 by omega]; simp

/-- `|finiteToRat s m e|` is the positive-sign value. -/
theorem abs_finiteToRat (s : Bool) (m : Nat) (e : Int) :
    (finiteToRat s m e).abs = finiteToRat false m e := by
  have h0 := finiteToRat_nonneg m e
  cases s
  · exact Rat.abs_of_nonneg h0
  · have : finiteToRat true m e = -finiteToRat false m e := by
      unfold finiteToRat; simp
    rw [this, Rat.abs_neg, Rat.abs_of_nonneg h0]

/-- `num`/`den` of `m * 2^e` agree with the unreduced pair `(m * 2^e⁺, 2^e⁻)` up to scaling. -/
theorem num_den_finiteToRat (m : Nat) (e : Int) :
    (finiteToRat false m e).num.toNat * 2 ^ (-e).toNat
      = m * 2 ^ e.toNat * (finiteToRat false m e).den := by
  have h := (Rat.mkRat_self (finiteToRat false m e)).trans (finiteToRat_false_eq_mkRat m e)
  rw [Rat.mkRat_eq_iff (Rat.den_nz _) (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))] at h
  have hnn : 0 ≤ (finiteToRat false m e).num := Rat.num_nonneg.mpr (finiteToRat_nonneg m e)
  have h' : (((finiteToRat false m e).num.toNat * 2 ^ (-e).toNat : Nat) : Int)
      = ((m * 2 ^ e.toNat * (finiteToRat false m e).den : Nat) : Int) := by
    push_cast; rw [Int.toNat_of_nonneg hnn]; exact h
  exact_mod_cast h'


/-- An exact quotient rounds to itself. -/
theorem roundQuot_mul_self (M : Nat) {D : Nat} (hD : 0 < D) : roundQuot (M * D) D = M := by
  unfold roundQuot
  rw [Nat.mul_div_cancel _ hD, Nat.mul_mod_left]
  simp [hD]

/-- `finalizeRounded` of a mantissa below `2 ^ fmt.prec` (no carry) at an exponent that does
not overflow is plain `encodeFinite`. -/
theorem finalizeRounded_of_lt (fmt : FloatFmt) (s : Bool) {m0 : Nat} {e0 : Int}
    (hm : m0 < 2 ^ fmt.prec) (he : e0 + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    Float.finalizeRounded fmt s (m0 : Int) e0 = Float.encodeFinite fmt s m0 e0 := by
  have hcast : ((2 : Nat) ^ fmt.prec : Int) = (2 : Int) ^ fmt.prec := by exact_mod_cast rfl
  have hne : (m0 : Int) ≠ (2 : Int) ^ fmt.prec := by rw [← hcast]; omega
  unfold Float.finalizeRounded
  rw [ite_eq_right hne]
  simp only [Int.toNat_natCast]
  rw [ite_eq_right (by omega)]


/-- Move a comparison against `n / d` over to `m * 2^e`, given `n * 2^y = m * 2^x * d`. -/
private theorem transfer_le {n d m x y a b : Nat} (hd : 0 < d) (hnd : n * 2 ^ y = m * 2 ^ x * d) :
    d * 2 ^ a ≤ n * 2 ^ b ↔ 1 * 2 ^ (a + y) ≤ m * 2 ^ (x + b) := by
  have e1 : d * 2 ^ a * 2 ^ y = d * (1 * 2 ^ (a + y)) := by
    rw [Nat.one_mul, Nat.pow_add, Nat.mul_assoc]
  have e2 : n * 2 ^ b * 2 ^ y = d * (m * 2 ^ (x + b)) := by
    rw [Nat.mul_right_comm, hnd, Nat.pow_add]; ac_rfl
  constructor
  · intro h
    have h1 := Nat.mul_le_mul_right (2 ^ y) h
    rw [e1, e2] at h1
    exact Nat.le_of_mul_le_mul_left h1 hd
  · intro h
    have h1 := Nat.mul_le_mul_left d h
    rw [← e1, ← e2] at h1
    exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos _)

/-- Equality form of `transfer_le`: `n / d = M * 2^-a` from `m * 2^e = M * 2^-a`. -/
private theorem transfer_eq {n d m x y a b M : Nat} (hnd : n * 2 ^ y = m * 2 ^ x * d)
    (h : m * 2 ^ (x + b) = M * 2 ^ (a + y)) : n * 2 ^ b = M * (d * 2 ^ a) := by
  have e1 : n * 2 ^ b * 2 ^ y = d * (m * 2 ^ (x + b)) := by
    rw [Nat.mul_right_comm, hnd, Nat.pow_add]; ac_rfl
  have e2 : M * (d * 2 ^ a) * 2 ^ y = d * (M * 2 ^ (a + y)) := by
    rw [Nat.pow_add]; ac_rfl
  apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos y)
  rw [e1, e2, h]


/-- Rounding an exactly representable magnitude `m * 2^e` (`0 < m < 2 ^ prec`, `e` in range):
`roundRat` normalizes it to `(m * 2^k) * 2^(e - k)` and encodes that, with no rounding step. -/
theorem roundRat_finiteToRat (fmt : FloatFmt) (s s' : Bool) {m : Nat} {e : Int}
    (hm0 : 0 < m) (hm : m < 2 ^ fmt.prec)
    (he_lo : fmt.emin - fmt.fracBits ≤ e) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    ∃ k : Nat, (k : Int) ≤ e - (fmt.emin - fmt.fracBits) ∧ m * 2 ^ k < 2 ^ fmt.prec ∧
      (2 ^ fmt.fracBits ≤ m * 2 ^ k ∨ e - k = fmt.emin - fmt.fracBits) ∧
      Float.roundRat fmt s (finiteToRat s' m e) = Float.encodeFinite fmt s (m * 2 ^ k) (e - k) := by
  have hnd := num_den_finiteToRat m e
  have hpos : 0 < m * 2 ^ e.toNat * (finiteToRat false m e).den :=
    Nat.mul_pos (Nat.mul_pos hm0 (Nat.two_pow_pos _)) (Rat.den_pos _)
  have hn : 0 < (finiteToRat false m e).num.toNat := by
    rcases Nat.eq_zero_or_pos (finiteToRat false m e).num.toNat with h | h
    · rw [h, Nat.zero_mul] at hnd; omega
    · exact h
  have hv0 : finiteToRat false m e ≠ 0 := by
    intro hc; rw [hc] at hn; simp at hn
  have hd : 0 < (finiteToRat false m e).den := Rat.den_pos _
  unfold Float.roundRat
  simp only [abs_finiteToRat, ite_eq_right hv0]
  generalize (finiteToRat false m e).num.toNat = n at hnd hn ⊢
  generalize (finiteToRat false m e).den = d at hnd hd hpos ⊢
  have hN_lt := roundRat_N_lt hn hd fmt.prec
    (Max.max (ilog2 n d - (fmt.prec - 1)) (fmt.emin - (fmt.prec - 1))) (Int.le_max_left _ _)
  have hspec := ilog2_spec hn hd
  generalize ilog2 n d = L at hspec hN_lt ⊢
  have hf : ((fmt.prec : Int) - 1) = fmt.fracBits := by
    simp only [FloatFmt.prec]; omega
  rw [hf] at hN_lt ⊢
  -- `n / d ≥ 2 ^ L`, moved over to `m * 2^e`.
  have hF1 : d * 2 ^ L.toNat ≤ n * 2 ^ (-L).toNat := by
    by_cases hL : 0 ≤ L
    · rw [show (-L).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]; exact (hspec.1 hL).1
    · rw [show L.toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]; exact (hspec.2 (by omega)).1
  have hT := (transfer_le hd hnd).mp hF1
  -- `L ≤ e + fracBits`: `m < 2 ^ prec`.
  have hLe : L ≤ e + fmt.fracBits := by
    apply Int.not_lt.mp
    intro hlt
    have h2 := (mul_pow_le_congr (x' := (L - e).toNat) (y' := 0) (by omega)).mp hT
    rw [Nat.pow_zero, Nat.mul_one, Nat.one_mul] at h2
    have h3 : 2 ^ fmt.prec ≤ 2 ^ (L - e).toNat :=
      Nat.pow_le_pow_right (by omega) (by simp only [FloatFmt.prec]; omega)
    omega
  generalize he0 : Max.max (L - fmt.fracBits) (fmt.emin - fmt.fracBits) = e0 at hN_lt ⊢
  have he0_lo : fmt.emin - fmt.fracBits ≤ e0 := he0 ▸ Int.le_max_right _ _
  have he0_L : L - fmt.fracBits ≤ e0 := he0 ▸ Int.le_max_left _ _
  have he0_or : e0 = L - fmt.fracBits ∨ e0 = fmt.emin - fmt.fracBits := by
    rw [← he0]; omega
  have he0_e : e0 ≤ e := by omega
  -- `N = M * D` with `M = m * 2 ^ (e - e0)`.
  have hND : (if e0 ≥ 0 then n else n <<< (-e0).toNat)
      = m * 2 ^ (e - e0).toNat * (if e0 ≥ 0 then d <<< e0.toNat else d) := by
    have hcore : n * 2 ^ (-e0).toNat = m * 2 ^ (e - e0).toNat * (d * 2 ^ e0.toNat) := by
      apply transfer_eq hnd
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    split
    · rw [Nat.shiftLeft_eq]; rw [show (-e0).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one] at hcore
      exact hcore
    · rw [Nat.shiftLeft_eq]; rw [show e0.toNat = 0 by omega, Nat.pow_zero, Nat.mul_one] at hcore
      exact hcore
  have hDpos : 0 < (if e0 ≥ 0 then d <<< e0.toNat else d) := by
    split
    · rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hd (Nat.two_pow_pos _)
    · exact hd
  have hMlt : m * 2 ^ (e - e0).toNat < 2 ^ fmt.prec := by
    rw [hND, Nat.mul_comm _ (2 ^ fmt.prec)] at hN_lt
    exact Nat.lt_of_mul_lt_mul_right hN_lt
  refine ⟨(e - e0).toNat, by omega, hMlt, ?_, ?_⟩
  · rcases he0_or with h | h
    · left
      have h2 := (mul_pow_le_congr (x' := fmt.fracBits) (y' := (e - e0).toNat) (by omega)).mp hT
      rw [Nat.one_mul] at h2; exact h2
    · right; omega
  · rw [hND, roundQuot_mul_self _ hDpos, show e - ((e - e0).toNat : Int) = e0 by omega]
    exact finalizeRounded_of_lt fmt s hMlt (by omega)


private theorem expBits_le_width_pred' (fmt : FloatFmt) : fmt.expBits ≤ fmt.width - 1 := by
  cases fmt <;> decide

/-- A float's bits are determined by its sign bit, exponent field and low bits. -/
private theorem toNat_decomp (fmt : FloatFmt) (x : Float fmt) :
    x.bits.toNat = 2 ^ (fmt.width - 1) * (if x.bits.msb then 1 else 0)
      + (x.bits.toNat % 2 ^ (fmt.width - 1 - fmt.expBits)
        + 2 ^ (fmt.width - 1 - fmt.expBits)
          * ((x.bits.toNat >>> (fmt.width - 1 - fmt.expBits)) % 2 ^ fmt.expBits)) := by
  have hw : 1 ≤ fmt.width := by cases fmt <;> decide
  have hR : (2 : Nat) ^ (fmt.width - 1) = 2 ^ (fmt.width - 1 - fmt.expBits) * 2 ^ fmt.expBits := by
    rw [← Nat.pow_add]; congr 1; have := expBits_le_width_pred' fmt; omega
  have hlt := x.bits.isLt
  have h2w : (2 : Nat) ^ fmt.width = 2 * 2 ^ (fmt.width - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hmsb := BitVec.msb_eq_decide x.bits
  have hq : x.bits.toNat / 2 ^ (fmt.width - 1) = if x.bits.msb then 1 else 0 := by
    rw [hmsb]
    have hp := Nat.two_pow_pos (fmt.width - 1)
    by_cases h : 2 ^ (fmt.width - 1) ≤ x.bits.toNat
    · simp only [h, decide_true, ↓reduceIte]
      apply Nat.le_antisymm
      · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by omega))
      · exact (Nat.le_div_iff_mul_le hp).mpr (by omega)
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [Nat.shiftRight_eq_div_pow, ← Nat.mod_mul, ← hR, ← hq]
  exact (Nat.div_add_mod _ _).symm

/-- Two floats with the same sign bit, exponent field and low bits are equal. -/
theorem Float.eq_of_fields {fmt : FloatFmt} {x y : Float fmt} (hs : x.bits.msb = y.bits.msb)
    (he : (x.bits.toNat >>> (fmt.width - 1 - fmt.expBits)) % 2 ^ fmt.expBits
      = (y.bits.toNat >>> (fmt.width - 1 - fmt.expBits)) % 2 ^ fmt.expBits)
    (hr : x.bits.toNat % 2 ^ (fmt.width - 1 - fmt.expBits)
      = y.bits.toNat % 2 ^ (fmt.width - 1 - fmt.expBits)) : x = y := by
  have h : x.bits = y.bits := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_decomp fmt x, toNat_decomp fmt y, hs, he, hr]
  cases x; cases y; simp only at h; rw [h]


/-- `classify` of a packed pattern, non-`f80`: `classify`'s own case split on the fields. -/
theorem classify_pack_of_ne_f80' {fmt : FloatFmt} (hf : fmt ≠ .f80) (s : Bool) {exp rest : Nat}
    (hexp : exp < 2 ^ fmt.expBits) (hrest : rest < 2 ^ fmt.fracBits) :
    (Float.pack fmt s exp rest).classify =
      if exp = 2 ^ fmt.expBits - 1 then (if rest = 0 then .inf s else .nan)
      else if exp = 0 then .finite s rest (fmt.emin - fmt.fracBits)
      else .finite s (2 ^ fmt.fracBits + rest) ((exp : Int) - fmt.bias - fmt.fracBits) := by
  have hrest' : rest < 2 ^ (fmt.width - 1 - fmt.expBits) := by rwa [restW_eq_fracBits fmt hf]
  obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec fmt s hexp hrest'
  rw [restW_eq_fracBits fmt hf] at hexpEq hrestEq
  cases fmt with
  | f80 => exact absurd rfl hf
  | f16 | f32 | f64 | f128 =>
    simp only [Float.classify]
    rw [expMask_succ, hexpEq, hrestEq, hmsb]

/-- `classify` of a packed `f80` pattern: `classify`'s own case split, with the integer bit
`rest / 2^63` and the fraction `rest % 2^63`. -/
theorem classify_pack_f80' (s : Bool) {exp rest : Nat}
    (hexp : exp < 2 ^ FloatFmt.f80.expBits) (hrest : rest < 2 ^ FloatFmt.f80.prec) :
    (Float.pack .f80 s exp rest).classify =
      if exp = 2 ^ FloatFmt.f80.expBits - 1 then
        (if rest / 2 ^ 63 = 0 then .nan else if rest % 2 ^ 63 = 0 then .inf s else .nan)
      else if rest / 2 ^ 63 = 0 then
        (if exp = 0 then .finite s (rest % 2 ^ 63) (FloatFmt.f80.emin - FloatFmt.f80.fracBits)
         else .nan)
      else if exp = 0 then .finite s (2 ^ 63 + rest % 2 ^ 63) (FloatFmt.f80.emin - FloatFmt.f80.fracBits)
      else .finite s (2 ^ 63 + rest % 2 ^ 63) ((exp : Int) - FloatFmt.f80.bias - FloatFmt.f80.fracBits) := by
  have hrest' : rest < 2 ^ (FloatFmt.f80.width - 1 - FloatFmt.f80.expBits) := by
    rw [restW_eq_fracBits_succ_f80]; exact hrest
  obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec .f80 s hexp hrest'
  rw [restW_eq_fracBits_succ_f80] at hexpEq hrestEq
  simp only [Float.classify]
  rw [expMask_succ, hexpEq, hmsb]
  generalize (Float.pack .f80 s exp rest).bits.toNat = v at hrestEq ⊢
  simp only [show FloatFmt.f80.fracBits = 63 from rfl, show FloatFmt.f80.prec = 64 from rfl,
    Nat.shiftRight_eq_div_pow] at hrestEq hrest ⊢
  have hv63 : v % 2 ^ 63 = rest % 2 ^ 63 := by
    rw [← hrestEq, Nat.mod_mod_of_dvd _ (by decide)]
  have hib : v / 2 ^ 63 % 2 = rest / 2 ^ 63 := by
    have := Nat.mod_add_div v (2 ^ 64)
    omega
  rw [hib, hv63]

/-- Every float is the `pack` of its own sign bit, exponent field and low bits. -/
theorem Float.eq_pack_fields {fmt : FloatFmt} (x : Float fmt) :
    x = Float.pack fmt x.bits.msb ((x.bits.toNat >>> (fmt.width - 1 - fmt.expBits)) % 2 ^ fmt.expBits)
      (x.bits.toNat % 2 ^ (fmt.width - 1 - fmt.expBits)) := by
  obtain ⟨_, hmsb, hexpEq, hrestEq⟩ := pack_bits_spec fmt x.bits.msb
    (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact Float.eq_of_fields hmsb.symm (by rw [hexpEq]) (by rw [hrestEq])


/-- Write `x` as `pack` of its fields, with the field bounds, for case analysis on `classify`. -/
private theorem exists_pack (x : Float fmt) :
    ∃ E F, E < 2 ^ fmt.expBits ∧ F < 2 ^ (fmt.width - 1 - fmt.expBits) ∧
      x = Float.pack fmt x.signBit E F ∧
      x.isPseudoDenormalF80 = (match fmt with
        | .f80 => F / 2 ^ 63 == 1 && E == 0
        | _ => false) := by
  refine ⟨_, _, Nat.mod_lt _ (Nat.two_pow_pos _), Nat.mod_lt _ (Nat.two_pow_pos _),
    Float.eq_pack_fields x, ?_⟩
  cases fmt with
  | f80 =>
    simp only [Float.isPseudoDenormalF80, restW_eq_fracBits_succ_f80,
      show FloatFmt.f80.fracBits = 63 from rfl, Nat.shiftRight_eq_div_pow]
    congr 2
    have := Nat.mod_add_div (x.bits.toNat) (2 ^ 64)
    omega
  | _ => rfl


/-- The mantissa/exponent range of every finite `classify` result: the exponent is at least the
subnormal one and at most `emax - fracBits`, and a mantissa below `2 ^ fracBits` sits at the
subnormal exponent. -/
theorem classify_finite_range {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) :
    fmt.emin - fmt.fracBits ≤ e ∧ e + (fmt.prec - 1 : Int) ≤ fmt.emax ∧
      (2 ^ fmt.fracBits ≤ m ∨ e = fmt.emin - fmt.fracBits) := by
  obtain ⟨E, F, hE, hF, hx, -⟩ := exists_pack x
  generalize x.signBit = sb at hx
  rw [hx] at h
  have hb : ∀ k : Nat, (2 : Nat) ^ (k + 1) - 1 - 1 - (2 ^ k - 1) = 2 ^ k - 1 := by
    intro k; rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := k); omega
  by_cases hf80 : fmt = .f80
  · subst hf80
    rw [restW_eq_fracBits_succ_f80] at hF
    rw [classify_pack_f80' sb hE hF] at h
    simp only [FloatFmt.emin, FloatFmt.emax, FloatFmt.prec, FloatFmt.bias, FloatFmt.fracBits,
      FloatFmt.expBits] at h hE hF ⊢
    by_cases hE1 : E = 2 ^ 15 - 1 <;> by_cases hI : F / 2 ^ 63 = 0 <;> by_cases hE0 : E = 0 <;>
      simp only [hE1, hI, hE0, ↓reduceIte, reduceCtorEq] at h <;> (try split at h) <;>
      (try cases h) <;>
      (try simp only [FloatClass.finite.injEq] at h) <;> (try obtain ⟨_, hm, he⟩ := h) <;> omega
  · rw [restW_eq_fracBits fmt hf80] at hF
    rw [classify_pack_of_ne_f80' hf80 sb hE hF] at h
    have hbias := hb (fmt.expBits - 1)
    have hEB : fmt.expBits - 1 + 1 = fmt.expBits := by cases fmt <;> decide
    rw [hEB] at hbias
    have : 2 ≤ 2 ^ (fmt.expBits - 1) := by cases fmt <;> decide
    simp only [FloatFmt.emin, FloatFmt.emax, FloatFmt.prec, FloatFmt.bias] at h ⊢
    by_cases hE1 : E = 2 ^ fmt.expBits - 1 <;> by_cases hE0 : E = 0 <;>
      simp only [hE1, hE0, ↓reduceIte] at h <;>
      (try split at h) <;> (try cases h) <;> (try simp only [FloatClass.finite.injEq] at h) <;>
      (try obtain ⟨_, hm, he⟩ := h) <;> omega


/-- A finite nonzero float is the `encodeFinite` of its own `classify` result, unless it is an
`f80` pseudo-denormal (a second encoding of a normal value, which `encodeFinite` never makes). -/
theorem encodeFinite_of_classify {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) (hm : m ≠ 0) (hc : x.isPseudoDenormalF80 = false) :
    Float.encodeFinite fmt s m e = x := by
  have hs := sign_of_classify_finite h
  obtain ⟨E, F, hE, hF, hx, hpd⟩ := exists_pack x
  rw [hc] at hpd
  generalize x.signBit = sb at hx hs
  subst hs
  rw [hx] at h ⊢
  unfold Float.encodeFinite
  rw [ite_eq_right hm]
  by_cases hf80 : fmt = .f80
  · subst hf80
    rw [restW_eq_fracBits_succ_f80] at hF
    rw [classify_pack_f80' s hE hF] at h
    have hE1 : E ≠ 2 ^ FloatFmt.f80.expBits - 1 := by
      intro hE1; rw [ite_eq_left hE1] at h; split at h <;> (try split at h) <;> cases h
    rw [ite_eq_right hE1] at h
    have hF64 : F < 2 ^ 64 := hF
    by_cases hI : F / 2 ^ 63 = 0
    · rw [ite_eq_left hI] at h
      by_cases hE0 : E = 0
      · rw [ite_eq_left hE0] at h
        injection h with _ hm' he
        subst hm' he hE0
        rw [ite_eq_left (show F % 2 ^ 63 < 2 ^ FloatFmt.f80.fracBits by simp only [FloatFmt.fracBits]; omega)]
        congr 1; omega
      · rw [ite_eq_right hE0] at h; cases h
    · rw [ite_eq_right hI] at h
      have hE0 : E ≠ 0 := by
        intro hE0; subst hE0
        have : F / 2 ^ 63 = 1 := by omega
        simp [this] at hpd
      rw [ite_eq_right hE0] at h
      injection h with _ hm' he
      subst hm' he
      rw [ite_eq_right (show ¬ (2 ^ 63 + F % 2 ^ 63 < 2 ^ FloatFmt.f80.fracBits) by
        simp only [FloatFmt.fracBits]; omega)]
      show Float.pack .f80 s _ (2 ^ 63 + F % 2 ^ 63) = Float.pack .f80 s E F
      simp only [FloatFmt.bias, FloatFmt.fracBits, FloatFmt.expBits]
      congr 1 <;> omega
  · rw [restW_eq_fracBits fmt hf80] at hF
    rw [classify_pack_of_ne_f80' hf80 s hE hF] at h
    have hE1 : E ≠ 2 ^ fmt.expBits - 1 := by
      intro hE1; rw [ite_eq_left hE1] at h; split at h <;> cases h
    rw [ite_eq_right hE1] at h
    by_cases hE0 : E = 0
    · rw [ite_eq_left hE0] at h
      injection h with _ hm' he
      subst hm' he hE0
      rw [ite_eq_left hF]
    · rw [ite_eq_right hE0] at h
      injection h with _ hm' he
      subst hm' he
      rw [ite_eq_right (show ¬ (2 ^ fmt.fracBits + F < 2 ^ fmt.fracBits) by omega)]
      have h1 : ((E : Int) - fmt.bias - fmt.fracBits + fmt.bias + fmt.fracBits).toNat = E := by
        omega
      have h2 : 2 ^ fmt.fracBits + F - 2 ^ fmt.fracBits = F := by omega
      cases fmt with
      | f80 => exact absurd rfl hf80
      | f16 | f32 | f64 | f128 => simp only [h1, h2]


/-- `finiteToRat` is invariant under moving a power of two from the exponent into the mantissa. -/
theorem finiteToRat_mul_pow (s : Bool) (m k : Nat) (e : Int) :
    finiteToRat s (m * 2 ^ k) (e - k) = finiteToRat s m e := by
  have hmag : finiteToRat false (m * 2 ^ k) (e - k) = finiteToRat false m e := by
    rw [finiteToRat_false_eq_mkRat, finiteToRat_false_eq_mkRat,
      Rat.mkRat_eq_iff (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
        (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))]
    have : m * 2 ^ k * 2 ^ (e - k).toNat * 2 ^ (-e).toNat
        = m * 2 ^ e.toNat * 2 ^ (-(e - k)).toNat := by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
      congr 2; omega
    exact_mod_cast this
  cases s
  · exact hmag
  · have hneg : ∀ m e, finiteToRat true m e = -finiteToRat false m e := by
      intro m e; unfold finiteToRat; simp
    rw [hneg, hneg, hmag]

/-- Rounding an exactly representable magnitude gives back that value, with the caller's sign.
`classify` may report it with a different (normalized) mantissa/exponent pair. -/
theorem roundRat_finiteToRat_classify (fmt : FloatFmt) (s s' : Bool) {m : Nat} {e : Int}
    (hm0 : 0 < m) (hm : m < 2 ^ fmt.prec)
    (he_lo : fmt.emin - fmt.fracBits ≤ e) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    ∃ m' e', (Float.roundRat fmt s (finiteToRat s' m e)).classify = .finite s m' e' ∧
      finiteToRat s m' e' = finiteToRat s m e := by
  obtain ⟨k, hk, hlt, hnorm, heq⟩ := roundRat_finiteToRat fmt s s' hm0 hm he_lo he_hi
  refine ⟨m * 2 ^ k, e - k, ?_, finiteToRat_mul_pow s m k e⟩
  rw [heq]
  exact classify_encodeFinite fmt s (Nat.mul_pos hm0 (Nat.two_pow_pos _)) hlt (by omega)
    (by omega) hnorm

/-- `toRat?` form of `roundRat_finiteToRat_classify`. -/
theorem roundRat_finiteToRat_toRat (fmt : FloatFmt) (s s' : Bool) {m : Nat} {e : Int}
    (hm0 : 0 < m) (hm : m < 2 ^ fmt.prec)
    (he_lo : fmt.emin - fmt.fracBits ≤ e) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax) :
    (Float.roundRat fmt s (finiteToRat s' m e)).toRat? = some (finiteToRat s m e) := by
  obtain ⟨m', e', hc, hv⟩ := roundRat_finiteToRat_classify fmt s s' hm0 hm he_lo he_hi
  unfold Float.toRat?; rw [hc]; exact congrArg some hv

/-- A canonical pair (normal mantissa, or the subnormal exponent) rounds to its own encoding. -/
theorem roundRat_finiteToRat_canonical (fmt : FloatFmt) (s s' : Bool) {m : Nat} {e : Int}
    (hm0 : 0 < m) (hm : m < 2 ^ fmt.prec)
    (he_lo : fmt.emin - fmt.fracBits ≤ e) (he_hi : e + (fmt.prec - 1 : Int) ≤ fmt.emax)
    (hnorm : 2 ^ fmt.fracBits ≤ m ∨ e = fmt.emin - fmt.fracBits) :
    Float.roundRat fmt s (finiteToRat s' m e) = Float.encodeFinite fmt s m e := by
  obtain ⟨k, hk, hlt, -, heq⟩ := roundRat_finiteToRat fmt s s' hm0 hm he_lo he_hi
  have hk0 : k = 0 := by
    rcases hnorm with h | h
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact h0
      · exfalso
        have h2 : 2 ^ fmt.prec ≤ m * 2 ^ k := by
          calc 2 ^ fmt.prec = 2 ^ fmt.fracBits * 2 ^ 1 := by
                rw [← Nat.pow_add]; rfl
            _ ≤ m * 2 ^ k := Nat.mul_le_mul h (Nat.pow_le_pow_right (by omega) h0)
        omega
    · omega
  rw [heq, hk0]; simp

/-- **Round trip.** Rounding the exact value of a finite nonzero float, with its own sign, gives
back the float itself — unless it is an `f80` pseudo-denormal, a non-canonical encoding (for
which see `roundRat_toRat_of_classify`). The sign of the `Rat` argument does not matter. -/
theorem roundRat_exact {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) (hm : m ≠ 0) (hc : x.isPseudoDenormalF80 = false)
    (s' : Bool) : Float.roundRat fmt s (finiteToRat s' m e) = x := by
  obtain ⟨he_lo, he_hi, hnorm⟩ := classify_finite_range h
  rw [roundRat_finiteToRat_canonical fmt s s' (Nat.pos_of_ne_zero hm) (classify_mantissa_lt h)
    he_lo he_hi hnorm]
  exact encodeFinite_of_classify h hm hc

/-- Round trip up to value, for every finite nonzero float (`f80` pseudo-denormals included):
the result has `x`'s value and `x`'s sign. -/
theorem roundRat_toRat_of_classify {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) (hm : m ≠ 0) (s' : Bool) :
    (Float.roundRat fmt s (finiteToRat s' m e)).toRat? = x.toRat? ∧
    (Float.roundRat fmt s (finiteToRat s' m e)).signBit = x.signBit := by
  obtain ⟨he_lo, he_hi, -⟩ := classify_finite_range h
  have hq : finiteToRat s' m e ≠ 0 := by
    intro h0
    have := abs_finiteToRat s' m e
    rw [h0] at this
    have hnd := num_den_finiteToRat m e
    rw [← this] at hnd
    have h3 : 0 < m * 2 ^ e.toNat * (Rat.abs 0).den :=
      Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos _)) (Rat.den_pos _)
    rw [← hnd] at h3
    simp at h3
  refine ⟨?_, ?_⟩
  · rw [roundRat_finiteToRat_toRat fmt s s' (Nat.pos_of_ne_zero hm) (classify_mantissa_lt h)
      he_lo he_hi]
    unfold Float.toRat?; rw [h]
  · rw [(roundRat_ne_zero_spec fmt s hq).2, sign_of_classify_finite h]

/-! ## Signed zeros -/

/-- A signed zero classifies as a zero mantissa at the subnormal exponent. -/
@[simp] theorem classify_zero {fmt : FloatFmt} (s : Bool) :
    (Float.zero s : Float fmt).classify = .finite s 0 (fmt.emin - fmt.fracBits) := by
  cases fmt <;> cases s <;> decide

/-- A zero mantissa denotes the `Rat` zero. -/
@[simp] theorem finiteToRat_zero (s : Bool) (e : Int) : finiteToRat s 0 e = 0 := by
  unfold finiteToRat; split <;> split <;> simp [Rat.div_def]

/-- A nonzero mantissa denotes a nonzero value. -/
theorem finiteToRat_ne_zero (s : Bool) {m : Nat} (hm : m ≠ 0) (e : Int) :
    finiteToRat s m e ≠ 0 := by
  intro h0
  have habs := abs_finiteToRat s m e
  rw [h0] at habs
  have hnd := num_den_finiteToRat m e
  rw [← habs] at hnd
  have h3 : 0 < m * 2 ^ e.toNat * (Rat.abs 0).den :=
    Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos _)) (Rat.den_pos _)
  rw [← hnd] at h3
  simp at h3

/-- The sign of a nonzero value is its sign flag. -/
theorem finiteToRat_lt_zero_iff (s : Bool) {m : Nat} (hm : m ≠ 0) (e : Int) :
    finiteToRat s m e < 0 ↔ s = true := by
  have h0 := finiteToRat_nonneg m e
  have hpos : 0 < finiteToRat false m e :=
    Rat.lt_of_le_of_ne h0 (Ne.symm (finiteToRat_ne_zero false hm e))
  cases s
  · simp only [Bool.false_eq_true, iff_false]; exact Rat.not_lt.mpr h0
  · have : finiteToRat true m e = -finiteToRat false m e := by unfold finiteToRat; simp
    rw [this]; simp only [iff_true]
    have := Rat.neg_lt_neg hpos
    rwa [Rat.neg_zero] at this

/-- A finite float with a zero mantissa is the signed zero of its sign. -/
theorem eq_zero_of_classify {fmt : FloatFmt} {x : Float fmt} {s : Bool} {e : Int}
    (h : x.classify = .finite s 0 e) : x = Float.zero s := by
  have hs := sign_of_classify_finite h
  obtain ⟨E, F, hE, hF, hx, -⟩ := exists_pack x
  generalize x.signBit = sb at hx hs
  subst hs
  rw [hx] at h ⊢
  unfold Float.zero
  by_cases hf80 : fmt = .f80
  · subst hf80
    rw [restW_eq_fracBits_succ_f80] at hF
    rw [classify_pack_f80' s hE hF] at h
    have hE1 : E ≠ 2 ^ FloatFmt.f80.expBits - 1 := by
      intro hE1; rw [ite_eq_left hE1] at h; split at h <;> (try split at h) <;> cases h
    rw [ite_eq_right hE1] at h
    have hF64 : F < 2 ^ 64 := hF
    by_cases hI : F / 2 ^ 63 = 0
    · rw [ite_eq_left hI] at h
      by_cases hE0 : E = 0
      · rw [ite_eq_left hE0] at h
        injection h with _ hm' _
        subst hE0
        congr 1; omega
      · rw [ite_eq_right hE0] at h; cases h
    · rw [ite_eq_right hI] at h
      split at h <;> (injection h with _ hm' _; omega)
  · rw [restW_eq_fracBits fmt hf80] at hF
    rw [classify_pack_of_ne_f80' hf80 s hE hF] at h
    have hE1 : E ≠ 2 ^ fmt.expBits - 1 := by
      intro hE1; rw [ite_eq_left hE1] at h; split at h <;> cases h
    rw [ite_eq_right hE1] at h
    split at h
    · injection h with _ hm' _
      subst hm'
      congr
    · injection h with _ hm' _
      have := Nat.two_pow_pos fmt.fracBits
      omega

/-- `x * (±0)` for finite `x` is the zero with the XOR of the signs. -/
theorem mul_zero_right {fmt : FloatFmt} {x : Float fmt} {sx : Bool} {mx : Nat} {ex : Int}
    (hx : x.classify = .finite sx mx ex) (s : Bool) :
    Float.mul x (Float.zero s) = Float.zero (sx != s) := by
  rw [mul_of_finite hx (classify_zero s), finiteToRat_zero, Rat.mul_zero, roundRat_zero]

/-- `x + (±0) = x` for finite `x` other than `-0` (`-0 + +0 = +0`), and not an `f80`
pseudo-denormal (the sum is re-encoded canonically). -/
theorem add_zero_right {fmt : FloatFmt} {x : Float fmt} {sx : Bool} {mx : Nat} {ex : Int}
    (hx : x.classify = .finite sx mx ex) (hx0 : x ≠ Float.zero true)
    (hc : x.isPseudoDenormalF80 = false) (s : Bool) :
    Float.add x (Float.zero s) = x := by
  unfold Float.add
  rw [hx, classify_zero]
  simp only [finiteToRat_zero, Rat.add_zero]
  by_cases hm : mx = 0
  · subst hm
    have hxz := eq_zero_of_classify hx
    have hsx : sx = false := by
      cases sx
      · rfl
      · exact absurd hxz hx0
    subst hsx
    rw [finiteToRat_zero, ite_eq_left rfl, roundRat_zero, hxz]
    simp
  · rw [ite_eq_right (finiteToRat_ne_zero sx hm ex)]
    have hsign : decide (finiteToRat sx mx ex < 0) = sx := by
      cases sx
      · exact decide_eq_false fun h =>
          absurd ((finiteToRat_lt_zero_iff false hm ex).mp h) Bool.false_ne_true
      · exact decide_eq_true ((finiteToRat_lt_zero_iff true hm ex).mpr rfl)
    rw [hsign]
    exact roundRat_exact hx hm hc sx

/-! ## Integers -/

/-- An integer is `finiteToRat` of its sign and magnitude at exponent `0`. -/
theorem intCast_eq_finiteToRat (v : Int) : (v : Rat) = finiteToRat (decide (v < 0)) v.natAbs 0 := by
  unfold finiteToRat
  simp only [show (0 : Int) ≥ 0 by decide, ↓reduceIte, Int.toNat_zero, Rat.pow_zero, Rat.mul_one]
  by_cases hv : v < 0
  · simp only [hv, decide_true, ↓reduceIte]
    have : v = -((v.natAbs : Nat) : Int) := by omega
    conv => lhs; rw [this]
    rw [Rat.intCast_neg, Rat.intCast_natCast]
  · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte]
    have : v = ((v.natAbs : Nat) : Int) := by omega
    conv => lhs; rw [this]
    rfl

/-- The fraction width never exceeds `emax - 1`, in every format: every integer up to
`2 ^ prec` sits in the normal range. -/
private theorem fracBits_add_one_le_emax (fmt : FloatFmt) : (fmt.fracBits : Int) + 1 ≤ fmt.emax := by
  cases fmt <;> decide

/-- Rounding an integer of at most `prec` bits (magnitude `≤ 2 ^ prec`) with its own sign is exact. -/
theorem roundRat_intCast_toRat (fmt : FloatFmt) (v : Int) (hv : v.natAbs ≤ 2 ^ fmt.prec) :
    (Float.roundRat fmt (decide (v < 0)) (v : Rat)).toRat? = some (v : Rat) := by
  have hfe := fracBits_add_one_le_emax fmt
  have hemin : fmt.emin - fmt.fracBits ≤ 0 := by cases fmt <;> decide
  have hp : ((fmt.prec : Int) - 1) = fmt.fracBits := by simp only [FloatFmt.prec]; omega
  by_cases h0 : v = 0
  · subst h0
    rw [show ((0 : Int) : Rat) = 0 from rfl, roundRat_zero]
    unfold Float.toRat?
    rw [classify_zero]
    exact congrArg some (finiteToRat_zero _ _)
  rw [intCast_eq_finiteToRat v]
  by_cases hlt : v.natAbs < 2 ^ fmt.prec
  · exact roundRat_finiteToRat_toRat fmt _ _ (by omega) hlt hemin (by omega)
  · have heq : v.natAbs = 2 ^ fmt.fracBits * 2 ^ 1 := by
      rw [← Nat.pow_add]; exact Nat.le_antisymm hv (Nat.not_lt.mp hlt)
    have hshift := finiteToRat_mul_pow (decide (v < 0)) (2 ^ fmt.fracBits) 1 1
    rw [show (1 : Int) - ((1 : Nat) : Int) = 0 by decide, ← heq] at hshift
    rw [hshift]
    exact roundRat_finiteToRat_toRat fmt _ _ (Nat.two_pow_pos _)
      (Nat.pow_lt_pow_right (by omega) (by simp only [FloatFmt.prec]; omega)) (by omega) (by omega)

/-- `@floatFromInt` is exact on integers of magnitude at most `2 ^ prec`. -/
theorem ofInt_exact {n : Nat} (fmt : FloatFmt) (s : Bool) (x : BitVec n)
    (h : (if s then x.toInt else (x.toNat : Int)).natAbs ≤ 2 ^ fmt.prec) :
    (Float.ofInt fmt s x).toRat? = some ((if s then x.toInt else (x.toNat : Int) : Int) : Rat) := by
  rw [ofInt_eq_roundRat]
  exact roundRat_intCast_toRat fmt _ h

/-! ## Monotonicity -/

/-- `roundQuot N D` is the floor `N / D` or one above it. -/
theorem roundQuot_bounds (N D : Nat) :
    ((N / D : Nat) : Int) ≤ roundQuot N D ∧ roundQuot N D ≤ ((N / D : Nat) : Int) + 1 := by
  unfold roundQuot
  simp only []
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- `roundQuot` is monotone in the fraction `N / D`. -/
theorem roundQuot_mono {N1 D1 N2 D2 : Nat} (hD1 : 0 < D1) (hD2 : 0 < D2)
    (h : N1 * D2 ≤ N2 * D1) : roundQuot N1 D1 ≤ roundQuot N2 D2 := by
  have hq : N1 / D1 ≤ N2 / D2 := by
    apply (Nat.le_div_iff_mul_le hD2).mpr
    have h1 : N1 / D1 * D1 ≤ N1 := Nat.div_mul_le_self N1 D1
    have h2 : N1 / D1 * D2 * D1 ≤ N2 * D1 := by
      calc N1 / D1 * D2 * D1 = N1 / D1 * D1 * D2 := Nat.mul_right_comm _ _ _
        _ ≤ N1 * D2 := Nat.mul_le_mul_right _ h1
        _ ≤ N2 * D1 := h
    exact Nat.le_of_mul_le_mul_right h2 hD1
  have b1 := roundQuot_bounds N1 D1
  have b2 := roundQuot_bounds N2 D2
  rcases Nat.lt_or_eq_of_le hq with hlt | heq
  · omega
  · -- Same floor `q`: compare the remainders.
    have e1 := Nat.div_add_mod N1 D1
    have e2 := Nat.div_add_mod N2 D2
    generalize hq1 : N1 / D1 = q at heq e1 b1 ⊢
    rw [heq] at hq1
    generalize hq2 : N2 / D2 = q' at heq e2 b2 ⊢
    subst heq
    generalize hr1 : N1 % D1 = r1 at e1 ⊢
    generalize hr2 : N2 % D2 = r2 at e2 ⊢
    have hr1lt : r1 < D1 := hr1 ▸ Nat.mod_lt _ hD1
    have hr2lt : r2 < D2 := hr2 ▸ Nat.mod_lt _ hD2
    have hr : r1 * D2 ≤ r2 * D1 := by
      have x1 : N1 * D2 = q * (D1 * D2) + r1 * D2 := by
        rw [← e1, Nat.add_mul]; ac_rfl
      have x2 : N2 * D1 = q * (D1 * D2) + r2 * D1 := by
        rw [← e2, Nat.add_mul]; ac_rfl
      omega
    unfold roundQuot
    simp only []
    rw [hr1, hr2, hq1, hq2]
    -- `2 r1 ≥ D1` forces `2 r2 ≥ D2`, strictly if strictly.
    have hlt : D1 < 2 * r1 → D2 < 2 * r2 := by
      intro h1
      have : D1 * D2 < D1 * (2 * r2) := by
        calc D1 * D2 < 2 * r1 * D2 := Nat.mul_lt_mul_of_pos_right h1 hD2
          _ = 2 * (r1 * D2) := Nat.mul_assoc _ _ _
          _ ≤ 2 * (r2 * D1) := Nat.mul_le_mul_left _ hr
          _ = D1 * (2 * r2) := by rw [Nat.mul_comm r2, ← Nat.mul_assoc, Nat.mul_comm 2 D1, Nat.mul_assoc]
      exact Nat.lt_of_mul_lt_mul_left this
    have hle : D1 ≤ 2 * r1 → D2 ≤ 2 * r2 := by
      intro h1
      have : D1 * D2 ≤ D1 * (2 * r2) := by
        calc D1 * D2 ≤ 2 * r1 * D2 := Nat.mul_le_mul_right _ h1
          _ = 2 * (r1 * D2) := Nat.mul_assoc _ _ _
          _ ≤ 2 * (r2 * D1) := Nat.mul_le_mul_left _ hr
          _ = D1 * (2 * r2) := by rw [Nat.mul_comm r2, ← Nat.mul_assoc, Nat.mul_comm 2 D1, Nat.mul_assoc]
      exact Nat.le_of_mul_le_mul_left this hD1
    split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- The lower `ilog2` bound `d * 2^L ≤ n` (shift form, `L : Int`). -/
theorem ilog2_low {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    d * 2 ^ (ilog2 n d).toNat ≤ n * 2 ^ (-ilog2 n d).toNat := by
  have hspec := ilog2_spec hn hd
  by_cases hL : 0 ≤ ilog2 n d
  · rw [show (-ilog2 n d).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]; exact (hspec.1 hL).1
  · rw [show (ilog2 n d).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]; exact (hspec.2 (by omega)).1

/-- `d * 2^a ≤ n` (shift form) is downward closed in `a`. -/
theorem shiftLe_mono {n d : Nat} {a b : Int} (hba : b ≤ a)
    (h : d * 2 ^ a.toNat ≤ n * 2 ^ (-a).toNat) : d * 2 ^ b.toNat ≤ n * 2 ^ (-b).toNat := by
  have h1 := (mul_pow_le_congr (x' := b.toNat + (a - b).toNat) (y' := (-b).toNat) (by omega)).mp h
  rw [Nat.pow_add, ← Nat.mul_assoc] at h1
  exact Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) h1

/-- `ilog2` is monotone in the fraction `n / d`. -/
theorem ilog2_mono {n1 d1 n2 d2 : Nat} (hn1 : 0 < n1) (hd1 : 0 < d1) (hn2 : 0 < n2)
    (hd2 : 0 < d2) (h : n1 * d2 ≤ n2 * d1) : ilog2 n1 d1 ≤ ilog2 n2 d2 := by
  apply Int.not_lt.mp
  intro hlt
  have hP := shiftLe_mono (show ilog2 n2 d2 + 1 ≤ ilog2 n1 d1 by omega) (ilog2_low hn1 hd1)
  have hL := ilog2_succ_bound hn2 hd2
  simp only [Nat.shiftLeft_eq] at hL
  generalize (ilog2 n2 d2 + 1).toNat = X at hP hL
  generalize (-(ilog2 n2 d2 + 1)).toNat = Y at hP hL
  -- `d1 2^X ≤ n1 2^Y`, `n2 2^Y < d2 2^X`, `n1 d2 ≤ n2 d1`: contradiction.
  have c1 : d1 * 2 ^ X * d2 ≤ n1 * 2 ^ Y * d2 := Nat.mul_le_mul_right _ hP
  have c2 : n1 * 2 ^ Y * d2 ≤ n2 * d1 * 2 ^ Y := by
    rw [Nat.mul_right_comm]; exact Nat.mul_le_mul_right _ h
  have c3 : n2 * d1 * 2 ^ Y < d2 * 2 ^ X * d1 := by
    rw [Nat.mul_right_comm]; exact Nat.mul_lt_mul_of_pos_right hL hd1
  have c4 : d2 * 2 ^ X * d1 = d1 * 2 ^ X * d2 := by ac_rfl
  omega

/-- Compare two nonnegative `finiteToRat` values through a common power of two. -/
theorem finiteToRat_false_le {a b : Nat} {x y : Int}
    (h : a * 2 ^ (x.toNat + (-y).toNat) ≤ b * 2 ^ (y.toNat + (-x).toNat)) :
    finiteToRat false a x ≤ finiteToRat false b y := by
  have hD : (2 : Nat) ^ ((-x).toNat + (-y).toNat) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  have e1 : finiteToRat false a x
      = mkRat ((a * 2 ^ (x.toNat + (-y).toNat) : Nat) : Int) (2 ^ ((-x).toNat + (-y).toNat)) := by
    rw [finiteToRat_false_eq_mkRat, Rat.mkRat_eq_iff (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)) hD]
    have : a * 2 ^ x.toNat * 2 ^ ((-x).toNat + (-y).toNat)
        = a * 2 ^ (x.toNat + (-y).toNat) * 2 ^ (-x).toNat := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
    exact_mod_cast this
  have e2 : finiteToRat false b y
      = mkRat ((b * 2 ^ (y.toNat + (-x).toNat) : Nat) : Int) (2 ^ ((-x).toNat + (-y).toNat)) := by
    rw [finiteToRat_false_eq_mkRat, Rat.mkRat_eq_iff (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)) hD]
    have : b * 2 ^ y.toNat * 2 ^ ((-x).toNat + (-y).toNat)
        = b * 2 ^ (y.toNat + (-x).toNat) * 2 ^ (-y).toNat := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
    exact_mod_cast this
  rw [e1, e2, Rat.mkRat_eq_div, Rat.mkRat_eq_div, Rat.div_def, Rat.div_def]
  apply Rat.mul_le_mul_of_nonneg_right
  · rw [Rat.intCast_natCast, Rat.intCast_natCast]; exact Rat.natCast_le_natCast.mpr h
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (by
      have := Nat.two_pow_pos ((-x).toNat + (-y).toNat)
      exact_mod_cast this))

/-- The value of a `finalizeRounded` result that is finite: `M * 2^e0`, for a mantissa
`M ≤ 2 ^ prec` (a negative `M` reads as `0`) that is normal or sits at the subnormal exponent. -/
theorem finalizeRounded_toRat (fmt : FloatFmt) (s : Bool) {M e0 : Int}
    (hM : M ≤ 2 ^ fmt.prec) (he_lo : fmt.emin - fmt.fracBits ≤ e0)
    (hnorm : 2 ^ fmt.fracBits ≤ M ∨ e0 = fmt.emin - fmt.fracBits) {r : Rat}
    (h : (Float.finalizeRounded fmt s M e0).toRat? = some r) : r = finiteToRat s M.toNat e0 := by
  have hcast : (((2 ^ fmt.prec : Nat)) : Int) = (2 : Int) ^ fmt.prec := by push_cast; rfl
  have hcastf : (((2 ^ fmt.fracBits : Nat)) : Int) = (2 : Int) ^ fmt.fracBits := by push_cast; rfl
  have hp : (2 : Nat) ^ fmt.prec = 2 ^ fmt.fracBits * 2 ^ 1 := by rw [← Nat.pow_add]; rfl
  have hpf : fmt.prec - 1 = fmt.fracBits := by simp only [FloatFmt.prec]; omega
  have hinf : ∀ neg, (Float.inf neg : Float fmt).toRat? = none := by
    intro neg; cases fmt <;> cases neg <;> decide
  unfold Float.finalizeRounded at h
  by_cases hc : M = (2 : Int) ^ fmt.prec
  · rw [ite_eq_left hc] at h
    simp only [] at h
    by_cases ho : e0 + 1 + ((fmt.prec : Int) - 1) > fmt.emax
    · rw [ite_eq_left ho, hinf] at h; cases h
    · rw [ite_eq_right ho, hpf] at h
      have hcl := classify_encodeFinite fmt s (m := 2 ^ fmt.fracBits) (e := e0 + 1)
        (Nat.two_pow_pos _) (by rw [hp]; have := Nat.two_pow_pos fmt.fracBits; omega)
        (by omega) (by omega) (Or.inl (Nat.le_refl _))
      unfold Float.toRat? at h
      rw [hcl] at h
      injection h with h
      rw [← h, hc, ← hcast, Int.toNat_natCast, hp]
      have := finiteToRat_mul_pow s (2 ^ fmt.fracBits) 1 (e0 + 1)
      rw [show e0 + 1 - ((1 : Nat) : Int) = e0 by omega] at this
      exact this.symm
  · rw [ite_eq_right hc] at h
    simp only [] at h
    by_cases ho : e0 + ((fmt.prec : Int) - 1) > fmt.emax
    · rw [ite_eq_left ho, hinf] at h; cases h
    · rw [ite_eq_right ho] at h
      by_cases hM0' : M.toNat = 0
      · rw [hM0'] at h ⊢
        unfold Float.encodeFinite at h
        rw [ite_eq_left rfl] at h
        unfold Float.toRat? at h
        rw [classify_zero] at h
        injection h with h
        rw [← h, finiteToRat_zero, finiteToRat_zero]
      · have hcl := classify_encodeFinite fmt s (m := M.toNat) (e := e0)
          (by omega) (by rw [← hcast] at hM hc; omega) he_lo (by omega)
          (by rw [← hcastf] at hnorm; omega)
        unfold Float.toRat? at h
        rw [hcl] at h
        injection h with h
        exact h.symm

/-- `roundRat`'s exponent for the fraction `n / d` (`n d` its numerator and denominator). -/
def roundExp (fmt : FloatFmt) (n d : Nat) : Int :=
  Max.max (ilog2 n d - ((fmt.prec : Int) - 1)) (fmt.emin - ((fmt.prec : Int) - 1))

/-- `roundRat`'s rounded mantissa for the fraction `n / d`, at exponent `roundExp fmt n d`. -/
def roundMant (fmt : FloatFmt) (n d : Nat) : Int :=
  let e0 := roundExp fmt n d
  roundQuot (n * 2 ^ (-e0).toNat) (d * 2 ^ e0.toNat)

/-- `roundRat` of a nonzero value, as `finalizeRounded` of `roundMant`/`roundExp`. -/
theorem roundRat_eq_finalize (fmt : FloatFmt) (s : Bool) {q : Rat} (hq : q ≠ 0) :
    Float.roundRat fmt s q = Float.finalizeRounded fmt s
      (roundMant fmt q.abs.num.toNat q.abs.den) (roundExp fmt q.abs.num.toNat q.abs.den) := by
  have habs : q.abs ≠ 0 := fun h => hq (Rat.abs_eq_zero_iff.mp h)
  unfold Float.roundRat roundMant roundExp
  simp only [ite_eq_right habs]
  generalize Max.max (ilog2 q.abs.num.toNat q.abs.den - ((fmt.prec : Int) - 1))
    (fmt.emin - ((fmt.prec : Int) - 1)) = e0
  congr 1
  split
  · rw [show (-e0).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one, Nat.shiftLeft_eq]
  · rw [show e0.toNat = 0 by omega, Nat.pow_zero, Nat.mul_one, Nat.shiftLeft_eq]

/-- `prec - 1 = fracBits`, over `Int`. -/
private theorem prec_sub_one (fmt : FloatFmt) : ((fmt.prec : Int) - 1) = fmt.fracBits := by
  simp only [FloatFmt.prec]; omega

/-- `roundExp` never goes below the subnormal exponent. -/
theorem roundExp_lo (fmt : FloatFmt) (n d : Nat) : fmt.emin - fmt.fracBits ≤ roundExp fmt n d := by
  unfold roundExp; rw [prec_sub_one]; exact Int.le_max_right _ _

/-- `roundMant` never exceeds `2 ^ prec` (the carry-out case reaches it). -/
theorem roundMant_le (fmt : FloatFmt) {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    roundMant fmt n d ≤ 2 ^ fmt.prec := by
  have h := roundRat_m0_le hn hd fmt.prec (roundExp fmt n d) (by unfold roundExp; exact Int.le_max_left _ _)
  unfold roundMant
  simp only []
  generalize roundExp fmt n d = e0 at h
  split at h
  · rwa [show (-e0).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one, ← Nat.shiftLeft_eq]
  · rwa [show e0.toNat = 0 by omega, Nat.pow_zero, Nat.mul_one, ← Nat.shiftLeft_eq]

/-- A mantissa off the subnormal exponent is normal: `n / d ≥ 2 ^ ilog2`, so the scaled
quotient is at least `2 ^ fracBits`. -/
theorem roundMant_norm (fmt : FloatFmt) {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    2 ^ fmt.fracBits ≤ roundMant fmt n d ∨ roundExp fmt n d = fmt.emin - fmt.fracBits := by
  have hlow := ilog2_low hn hd
  have hor : roundExp fmt n d = ilog2 n d - fmt.fracBits ∨
      roundExp fmt n d = fmt.emin - fmt.fracBits := by
    unfold roundExp; rw [prec_sub_one]; omega
  rcases hor with he | he
  · left
    unfold roundMant
    simp only []
    rw [he]
    generalize ilog2 n d = L at hlow ⊢
    have hDpos : 0 < d * 2 ^ (L - fmt.fracBits).toNat := Nat.mul_pos hd (Nat.two_pow_pos _)
    have hN : 2 ^ fmt.fracBits * (d * 2 ^ (L - fmt.fracBits).toNat)
        ≤ n * 2 ^ (-(L - fmt.fracBits)).toNat := by
      have h1 := (mul_pow_le_congr (x' := (L - fmt.fracBits).toNat + fmt.fracBits)
        (y' := (-(L - fmt.fracBits)).toNat) (by omega)).mp hlow
      rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm (d * _)] at h1
      exact h1
    have hdiv : 2 ^ fmt.fracBits ≤ n * 2 ^ (-(L - fmt.fracBits)).toNat
        / (d * 2 ^ (L - fmt.fracBits).toNat) := (Nat.le_div_iff_mul_le hDpos).mpr hN
    have hb := (roundQuot_bounds (n * 2 ^ (-(L - fmt.fracBits)).toNat)
      (d * 2 ^ (L - fmt.fracBits).toNat)).1
    have hcastf : (((2 ^ fmt.fracBits : Nat)) : Int) = (2 : Int) ^ fmt.fracBits := by
      push_cast; rfl
    omega
  · exact Or.inr he

/-- The value of a finite `roundRat` result of a nonzero `q`: `roundMant * 2 ^ roundExp`. -/
theorem roundRat_toRat_value (fmt : FloatFmt) (s : Bool) {q r : Rat} (hq : q ≠ 0)
    (h : (Float.roundRat fmt s q).toRat? = some r) :
    r = finiteToRat s (roundMant fmt q.abs.num.toNat q.abs.den).toNat
      (roundExp fmt q.abs.num.toNat q.abs.den) := by
  have habs : q.abs ≠ 0 := fun h => hq (Rat.abs_eq_zero_iff.mp h)
  have hnn : 0 ≤ q.abs.num := Rat.num_nonneg.mpr Rat.abs_nonneg
  have hn : 0 < q.abs.num.toNat := by
    have : q.abs.num ≠ 0 := fun h0 => habs (Rat.num_eq_zero.mp h0)
    omega
  rw [roundRat_eq_finalize fmt s hq] at h
  exact finalizeRounded_toRat fmt s (roundMant_le fmt hn (Rat.den_pos _)) (roundExp_lo fmt _ _)
    (roundMant_norm fmt hn (Rat.den_pos _)) h

/-- `n / d` of a positive rational, cross-multiplied: `q1 ≤ q2` on numerators/denominators. -/
private theorem num_den_le {q1 q2 : Rat} (h0 : 0 ≤ q1) (h : q1 ≤ q2) :
    q1.num.toNat * q2.den ≤ q2.num.toNat * q1.den := by
  have h1 := (Rat.le_iff q1 q2).mp h
  have hn1 : 0 ≤ q1.num := Rat.num_nonneg.mpr h0
  have hn2 : 0 ≤ q2.num := Rat.num_nonneg.mpr (Rat.le_trans h0 h)
  have : ((q1.num.toNat * q2.den : Nat) : Int) ≤ ((q2.num.toNat * q1.den : Nat) : Int) := by
    push_cast; rw [Int.toNat_of_nonneg hn1, Int.toNat_of_nonneg hn2]; exact h1
  exact_mod_cast this

/-- **Monotonicity** of rounding on nonnegative values: `0 ≤ q1 ≤ q2`, both results finite, then
the rounded values are ordered the same way. -/
theorem roundRat_mono (fmt : FloatFmt) {q1 q2 r1 r2 : Rat} (h0 : 0 ≤ q1) (h12 : q1 ≤ q2)
    (h1 : (Float.roundRat fmt false q1).toRat? = some r1)
    (h2 : (Float.roundRat fmt false q2).toRat? = some r2) : r1 ≤ r2 := by
  by_cases hq1 : q1 = 0
  · subst hq1
    rw [roundRat_zero] at h1
    unfold Float.toRat? at h1
    rw [classify_zero] at h1
    injection h1 with h1
    rw [← h1, finiteToRat_zero]
    by_cases hq2 : q2 = 0
    · subst hq2
      rw [roundRat_zero] at h2
      unfold Float.toRat? at h2
      rw [classify_zero] at h2
      injection h2 with h2
      rw [← h2, finiteToRat_zero]; exact Rat.le_refl
    · rw [roundRat_toRat_value fmt false hq2 h2]; exact finiteToRat_nonneg _ _
  have hpos1 : 0 < q1 := Rat.lt_of_le_of_ne h0 (Ne.symm hq1)
  have hq2 : q2 ≠ 0 := fun h => by subst h; exact absurd (Rat.le_antisymm h12 h0) hq1
  have h0' : 0 ≤ q2 := Rat.le_trans h0 h12
  rw [roundRat_toRat_value fmt false hq1 h1, roundRat_toRat_value fmt false hq2 h2,
    Rat.abs_of_nonneg h0, Rat.abs_of_nonneg h0']
  have hnd := num_den_le h0 h12
  have hn1 : 0 < q1.num.toNat := by
    have := Rat.num_nonneg.mpr h0
    have : q1.num ≠ 0 := fun h => hq1 (Rat.num_eq_zero.mp h)
    omega
  have hn2 : 0 < q2.num.toNat := by
    have := Rat.num_nonneg.mpr h0'
    have : q2.num ≠ 0 := fun h => hq2 (Rat.num_eq_zero.mp h)
    omega
  have hd1 := q1.den_pos
  have hd2 := q2.den_pos
  generalize q1.num.toNat = n1 at hnd hn1
  generalize q2.num.toNat = n2 at hnd hn2
  generalize q1.den = d1 at hnd hd1
  generalize q2.den = d2 at hnd hd2
  have hL := ilog2_mono hn1 hd1 hn2 hd2 hnd
  have he12 : roundExp fmt n1 d1 ≤ roundExp fmt n2 d2 := by
    unfold roundExp; omega
  have hM1 := roundMant_le fmt hn1 hd1
  have hM2n := roundMant_norm fmt hn2 hd2
  have hlo1 := roundExp_lo fmt n1 d1
  rcases Int.lt_or_eq_of_le he12 with hlt | heq
  · -- Different exponents: `M1 * 2^e1 ≤ 2^prec * 2^e1 ≤ 2^fracBits * 2^e2 ≤ M2 * 2^e2`.
    have hM2 : 2 ^ fmt.fracBits ≤ roundMant fmt n2 d2 := by
      rcases hM2n with h | h
      · exact h
      · omega
    have hcast : (((2 ^ fmt.prec : Nat)) : Int) = (2 : Int) ^ fmt.prec := by push_cast; rfl
    have hcastf : (((2 ^ fmt.fracBits : Nat)) : Int) = (2 : Int) ^ fmt.fracBits := by
      push_cast; rfl
    have hp1 : (0 : Int) < 2 ^ fmt.prec := hcast ▸ Int.natCast_pos.mpr (Nat.two_pow_pos _)
    have hM1' : (roundMant fmt n1 d1).toNat ≤ 2 ^ fmt.prec := by omega
    have hM2' : 2 ^ fmt.fracBits ≤ (roundMant fmt n2 d2).toNat := by omega
    apply finiteToRat_false_le
    generalize roundExp fmt n1 d1 = e1 at hlt hlo1
    generalize roundExp fmt n2 d2 = e2 at hlt
    calc (roundMant fmt n1 d1).toNat * 2 ^ (e1.toNat + (-e2).toNat)
        ≤ 2 ^ fmt.prec * 2 ^ (e1.toNat + (-e2).toNat) := Nat.mul_le_mul_right _ hM1'
      _ = 2 ^ (fmt.prec + (e1.toNat + (-e2).toNat)) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (fmt.fracBits + (e2.toNat + (-e1).toNat)) :=
          Nat.pow_le_pow_right (by omega) (by simp only [FloatFmt.prec]; omega)
      _ = 2 ^ fmt.fracBits * 2 ^ (e2.toNat + (-e1).toNat) := Nat.pow_add _ _ _
      _ ≤ (roundMant fmt n2 d2).toNat * 2 ^ (e2.toNat + (-e1).toNat) := Nat.mul_le_mul_right _ hM2'
  · -- Same exponent `E`: `roundQuot` is monotone.
    have hmono : roundMant fmt n1 d1 ≤ roundMant fmt n2 d2 := by
      unfold roundMant
      simp only []
      rw [heq]
      generalize roundExp fmt n2 d2 = E
      apply roundQuot_mono (Nat.mul_pos hd1 (Nat.two_pow_pos _)) (Nat.mul_pos hd2 (Nat.two_pow_pos _))
      calc n1 * 2 ^ (-E).toNat * (d2 * 2 ^ E.toNat) = n1 * d2 * (2 ^ (-E).toNat * 2 ^ E.toNat) := by
            ac_rfl
        _ ≤ n2 * d1 * (2 ^ (-E).toNat * 2 ^ E.toNat) := Nat.mul_le_mul_right _ hnd
        _ = n2 * 2 ^ (-E).toNat * (d1 * 2 ^ E.toNat) := by ac_rfl
    apply finiteToRat_false_le
    rw [heq]
    exact Nat.mul_le_mul_right _ (by omega)

end Zig
