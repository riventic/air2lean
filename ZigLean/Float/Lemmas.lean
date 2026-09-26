import ZigLean.Float.Ops

/-!
# Float model lemmas

A lemma library about the executable IEEE-754 model (`docs/floats.md`), for proofs about
generated code that uses floats (`Proofs/Floats`, `Proofs/Floatops`, `Proofs/Floatconv`).
-/

namespace Zig

variable {fmt : FloatFmt}

/-! ## Classification -/

/-- `isNaN` characterizes `classify`. -/
theorem isNaN_iff (x : Float fmt) : x.isNaN = true ↔ x.classify = .nan := by
  unfold Float.isNaN
  cases x.classify <;> simp

/-- The canonical NaN classifies as NaN. -/
@[simp] theorem isNaN_nan : (Float.nan : Float fmt).isNaN = true := by
  cases fmt <;> decide

/-- `ofBits` after `.bits` is the identity. -/
@[simp] theorem ofBits_bits (x : Float fmt) : Float.ofBits x.bits = x := rfl

/-- `.bits` after `ofBits` is the identity. -/
@[simp] theorem bits_ofBits (b : BitVec fmt.width) : (Float.ofBits b).bits = b := rfl

/-- `x = x` iff `x` is not NaN (`Float.eq`'s only unordered case). -/
theorem eq_self (x : Float fmt) : Float.eq x x = !x.isNaN := by
  unfold Float.eq Float.isNaN
  cases x.classify <;> simp

/-- `isNaN` in terms of `Float.eq` being reflexive or not. -/
theorem isNaN_iff_not_eq_self (x : Float fmt) : x.isNaN = true ↔ Float.eq x x = false := by
  rw [eq_self]; cases x.isNaN <;> simp

/-- `Float.ne` is the negation of `Float.eq` (definitional). -/
@[simp] theorem ne_eq_not_eq (a b : Float fmt) : Float.ne a b = !Float.eq a b := rfl

/-! ## Compares against `Rat`

`toRat?` is `some` only for a finite value; the following state each compare's finite case in
terms of the `Rat` values, and the NaN case (always false, except `ne`) separately. -/

/-- A value with `toRat? = some a` is finite, with `a` its exact value. -/
theorem exists_finite_of_toRat? {x : Float fmt} {a : Rat} (h : x.toRat? = some a) :
    ∃ s m e, x.classify = .finite s m e ∧ finiteToRat s m e = a := by
  unfold Float.toRat? at h
  revert h
  cases hc : x.classify with
  | nan => simp
  | inf s => simp
  | finite s m e => intro h; exact ⟨s, m, e, rfl, by simpa using h⟩

theorem lt_of_toRat {x y : Float fmt} {a b : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) : Float.lt x y = decide (a < b) := by
  obtain ⟨sa, ma, ea, hxc, hxv⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, hyv⟩ := exists_finite_of_toRat? hy
  unfold Float.lt
  simp [hxc, hyc, hxv, hyv]

theorem eq_of_toRat {x y : Float fmt} {a b : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) : Float.eq x y = decide (a = b) := by
  obtain ⟨sa, ma, ea, hxc, hxv⟩ := exists_finite_of_toRat? hx
  obtain ⟨sb, mb, eb, hyc, hyv⟩ := exists_finite_of_toRat? hy
  unfold Float.eq
  simp [hxc, hyc, hxv, hyv, BEq.beq]

theorem le_of_toRat {x y : Float fmt} {a b : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) : Float.le x y = decide (a ≤ b) := by
  unfold Float.le
  simp [lt_of_toRat hx hy, eq_of_toRat hx hy, Rat.le_iff_lt_or_eq]

theorem gt_of_toRat {x y : Float fmt} {a b : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) : Float.gt x y = decide (a > b) := by
  unfold Float.gt
  exact lt_of_toRat hy hx

theorem ge_of_toRat {x y : Float fmt} {a b : Rat} (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) : Float.ge x y = decide (a ≥ b) := by
  unfold Float.ge
  exact le_of_toRat hy hx

/-! NaN comparisons: unordered (`false` on either side), except `ne` (`true`). -/

theorem eq_false_of_isNaN_left {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    Float.eq x y = false := by
  unfold Float.eq; rw [(isNaN_iff x).mp h]

theorem eq_false_of_isNaN_right (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    Float.eq x y = false := by
  unfold Float.eq; rw [(isNaN_iff y).mp h]; cases x.classify <;> rfl

theorem lt_false_of_isNaN_left {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    Float.lt x y = false := by
  unfold Float.lt; rw [(isNaN_iff x).mp h]

theorem lt_false_of_isNaN_right (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    Float.lt x y = false := by
  unfold Float.lt; rw [(isNaN_iff y).mp h]; cases x.classify <;> rfl

theorem le_false_of_isNaN_left {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    Float.le x y = false := by
  unfold Float.le; simp [lt_false_of_isNaN_left h y, eq_false_of_isNaN_left h y]

theorem le_false_of_isNaN_right (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    Float.le x y = false := by
  unfold Float.le; simp [lt_false_of_isNaN_right x h, eq_false_of_isNaN_right x h]

theorem gt_false_of_isNaN_left {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    Float.gt x y = false := by
  unfold Float.gt; exact lt_false_of_isNaN_right y h

theorem gt_false_of_isNaN_right (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    Float.gt x y = false := by
  unfold Float.gt; exact lt_false_of_isNaN_left h x

theorem ge_false_of_isNaN_left {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    Float.ge x y = false := by
  unfold Float.ge; exact le_false_of_isNaN_right y h

theorem ge_false_of_isNaN_right (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    Float.ge x y = false := by
  unfold Float.ge; exact le_false_of_isNaN_left h x

theorem ne_true_of_isNaN_left {x : Float fmt} (h : x.isNaN = true) (y : Float fmt) :
    Float.ne x y = true := by
  simp [eq_false_of_isNaN_left h y]

theorem ne_true_of_isNaN_right (x : Float fmt) {y : Float fmt} (h : y.isNaN = true) :
    Float.ne x y = true := by
  simp [eq_false_of_isNaN_right x h]

/-! ## Format bit-width facts -/

private theorem width_pos (fmt : FloatFmt) : 0 < fmt.width := by cases fmt <;> decide

private theorem expBits_le_width_pred (fmt : FloatFmt) : fmt.expBits ≤ fmt.width - 1 := by
  cases fmt <;> decide

/-! ## Rounding -/

/-- Rounding zero gives a signed zero (`roundRat`'s own first branch). -/
@[simp] theorem roundRat_zero (fmt : FloatFmt) (neg : Bool) :
    Float.roundRat fmt neg 0 = Float.zero neg := by
  unfold Float.roundRat; simp

/-! ## Canonical encodings: sign bit and classification -/

@[simp] theorem signBit_zero (neg : Bool) : (Float.zero (fmt := fmt) neg).signBit = neg := by
  cases fmt <;> cases neg <;> decide

@[simp] theorem isNaN_zero (neg : Bool) : (Float.zero (fmt := fmt) neg).isNaN = false := by
  cases fmt <;> cases neg <;> decide

@[simp] theorem signBit_inf (neg : Bool) : (Float.inf (fmt := fmt) neg).signBit = neg := by
  cases fmt <;> cases neg <;> decide

@[simp] theorem isNaN_inf (neg : Bool) : (Float.inf (fmt := fmt) neg).isNaN = false := by
  cases fmt <;> cases neg <;> decide

/-- `roundRat`'s result with a `false` sign is never NaN and never negative-zero: `q = 0` reduces
to `Float.zero false` (`roundRat_zero`); `q ≠ 0` is `roundRat_ne_zero_spec`. -/
theorem roundRat_nonneg (fmt : FloatFmt) (q : Rat) :
    (Float.roundRat fmt false q).isNaN = false ∧ (Float.roundRat fmt false q).signBit = false := by
  by_cases hq : q = 0
  · subst hq; simp
  · exact roundRat_ne_zero_spec fmt false hq

/-- Packing preserves the sign bit, given the exponent field and low bits fit their width (so
the OR never spills into the sign bit at position `width - 1`). -/
theorem signBit_pack {sign : Bool} {exp rest : Nat} (hexp : exp < 2 ^ fmt.expBits)
    (hrest : rest < 2 ^ (fmt.width - 1 - fmt.expBits)) :
    (Float.pack fmt sign exp rest).signBit = sign := by
  unfold Float.pack Float.signBit
  rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  have hw : fmt.expBits + (fmt.width - 1 - fmt.expBits) = fmt.width - 1 := by
    have := expBits_le_width_pred fmt; omega
  have hexp' : exp <<< (fmt.width - 1 - fmt.expBits) < 2 ^ (fmt.width - 1) := by
    rw [Nat.shiftLeft_eq]
    have heq : (2 : Nat) ^ fmt.expBits * 2 ^ (fmt.width - 1 - fmt.expBits) = 2 ^ (fmt.width - 1) := by
      rw [← Nat.pow_add, hw]
    rw [← heq]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hexp
  have hrest' : rest < 2 ^ (fmt.width - 1) := by
    have h := Nat.pow_le_pow_right (n := 2) (by omega)
      (show fmt.width - 1 - fmt.expBits ≤ fmt.width - 1 by omega)
    omega
  have hor : exp <<< (fmt.width - 1 - fmt.expBits) ||| rest < 2 ^ (fmt.width - 1) :=
    Nat.or_lt_two_pow hexp' hrest'
  have hw1 : (2 : Nat) ^ (fmt.width - 1) < 2 ^ fmt.width :=
    Nat.pow_lt_pow_right (by omega) (by have := width_pos fmt; omega)
  rw [Nat.or_assoc]
  cases sign with
  | false =>
    simp [Nat.zero_shiftLeft, Nat.zero_or]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hor
  | true =>
    simp [Nat.one_shiftLeft]
    have hbound : (2 : Nat) ^ (fmt.width - 1) ||| (exp <<< (fmt.width - 1 - fmt.expBits) ||| rest)
        < 2 ^ fmt.width := Nat.or_lt_two_pow hw1 (by omega)
    rw [Nat.mod_eq_of_lt hbound]
    exact Nat.left_le_or

/-! ## Sign-bit-only ops -/

private theorem neg_bits_eq_xor (x : Float fmt) :
    (Float.neg x).bits = x.bits ^^^ BitVec.ofNat fmt.width (1 <<< (fmt.width - 1)) := by
  unfold Float.neg
  rw [BitVec.ofNat_xor, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `neg` is an involution, at the bit level (`docs/floats.md`: `neg` only flips the sign
bit, so this holds for NaN too, not just finite/infinite values). -/
@[simp] theorem neg_neg (x : Float fmt) : (Float.neg (Float.neg x)).bits = x.bits := by
  simp [neg_bits_eq_xor, BitVec.xor_assoc]

/-- `abs`'s result is never negative (`abs` only clears the sign bit). -/
@[simp] theorem signBit_abs_eq_false (x : Float fmt) : (Float.abs x).signBit = false := by
  unfold Float.abs Float.signBit
  rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  have hlt : x.bits.toNat % 2 ^ (fmt.width - 1) < 2 ^ (fmt.width - 1) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hle : (2 : Nat) ^ (fmt.width - 1) ≤ 2 ^ fmt.width :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_false (Nat.not_le.mpr hlt)

/-! ## Arithmetic

Finite operands, restated in terms of `Float.roundRat` (`docs/floats.md` §Semantics: every
arithmetic op rounds its exact `Rat` result once). `add`'s sign has a signed-zero special case
(`x + (-x) = +0` unless both operands are `-0`), so its sign is stated existentially rather than
by a closed formula; `mul`/`div` have none (the sign is always the XOR of the operand signs). -/

theorem add_of_finite {sa sb : Bool} {ma mb : Nat} {ea eb : Int} {x y : Float fmt}
    (hx : x.classify = .finite sa ma ea) (hy : y.classify = .finite sb mb eb) :
    ∃ neg : Bool,
      Float.add x y = Float.roundRat fmt neg (finiteToRat sa ma ea + finiteToRat sb mb eb) := by
  unfold Float.add
  rw [hx, hy]
  exact ⟨_, rfl⟩

/-- `sub` is `add` of the negation, literally (`Float.sub`'s own definition). -/
theorem sub_eq_add_neg (x y : Float fmt) : Float.sub x y = Float.add x (Float.neg y) := rfl

theorem mul_of_finite {sa sb : Bool} {ma mb : Nat} {ea eb : Int} {x y : Float fmt}
    (hx : x.classify = .finite sa ma ea) (hy : y.classify = .finite sb mb eb) :
    Float.mul x y = Float.roundRat fmt (sa != sb) (finiteToRat sa ma ea * finiteToRat sb mb eb) := by
  unfold Float.mul
  rw [hx, hy]

theorem div_of_finite {sa sb : Bool} {ma mb : Nat} {ea eb : Int} {x y : Float fmt}
    (hx : x.classify = .finite sa ma ea) (hy : y.classify = .finite sb mb eb) (hb : mb ≠ 0) :
    Float.div x y = Float.roundRat fmt (sa != sb) (finiteToRat sa ma ea / finiteToRat sb mb eb) := by
  unfold Float.div
  rw [hx, hy]
  simp [hb]

/-! ## Conversions -/

/-- `@floatToInt`, restated for a finite operand: the exact truncation-and-range-check
`Float.toInt` performs, with `x`'s classification substituted in. -/
theorem toInt_of_finite {s : Bool} {n : Nat} {safe : Bool} {sn : Bool} {m : Nat} {e : Int}
    {x : Float fmt} (hx : x.classify = .finite sn m e) :
    Float.toInt s n safe x =
      let mag : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
      let tv : Int := if sn then -(mag : Int) else (mag : Int)
      let lo : Int := if s then -(2 ^ (n - 1) : Int) else 0
      let hi : Int := if s then (2 ^ (n - 1) : Int) - 1 else (2 ^ n : Int) - 1
      if tv < lo || tv > hi then
        if safe then throw .overflow else throw .unspecified
      else pure (BitVec.ofInt n tv) := by
  unfold Float.toInt
  rw [hx]

/-- `@intToFloat`, restated as its own definition unfolded: `ofInt` never special-cases `v = 0`
because `roundRat` already gives `+0` for a zero input (`roundRat_zero`). -/
theorem ofInt_eq_roundRat {n : Nat} (s : Bool) (x : BitVec n) :
    Float.ofInt fmt s x =
      Float.roundRat fmt ((if s then x.toInt else (x.toNat : Int)) < 0)
        ((if s then x.toInt else (x.toNat : Int) : Int) : Rat) := by
  unfold Float.ofInt
  simp

/-! ## `truncRat`

Truncation toward zero of an exact `Rat`, shared by `Float.trunc`/`Float.rem` and (via
`toInt_of_toRat` below) by `@floatToInt`. -/

/-- The `Nat` floor of `m / 2^k` (as a `Rat`) is the `Nat` division `m / 2^k`. -/
theorem floor_natCast_div_pow (m k : Nat) :
    ((m : Rat) / (2 : Rat) ^ k).floor = ((m / 2 ^ k : Nat) : Int) := by
  have h2 : (0:Rat) < (2:Rat)^k := by
    have : (0:Nat) < 2^k := Nat.two_pow_pos k
    exact_mod_cast this
  have hlow : (m / 2^k) * 2 ^ k ≤ m := Nat.div_mul_le_self m (2 ^ k)
  have hmod : m % 2 ^ k < 2 ^ k := Nat.mod_lt m (Nat.two_pow_pos k)
  have haddmod : (m / 2^k) * 2 ^ k + m % 2 ^ k = m := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod m (2 ^ k)
  have hhigh : m < (m / 2^k + 1) * 2 ^ k := by
    rw [Nat.succ_mul]; omega
  have e1 : ((m/2^k : Nat) : Int) ≤ ((m:Rat)/(2:Rat)^k).floor := by
    rw [Rat.le_floor_iff, ← Rat.not_lt, Rat.div_lt_iff h2]
    intro hc
    have hc' : m < (m/2^k) * 2^k := by exact_mod_cast hc
    omega
  have e2 : ((m:Rat)/(2:Rat)^k).floor < ((m/2^k : Nat):Int) + 1 := by
    rw [Rat.floor_lt_iff, Rat.div_lt_iff h2]
    exact_mod_cast hhigh
  omega

/-- The magnitude Nat that `Float.toInt`/`finiteToRat` compute (`if e ≥ 0 then m*2^e.toNat else
m/2^(-e).toNat`) is `⌊mag_rat⌋`, where `mag_rat` is that same value computed exactly in `Rat`. -/
theorem floor_magRat (m : Nat) (e : Int) :
    ((if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)).floor =
      ((if e ≥ 0 then m * 2^e.toNat else m / 2^(-e).toNat : Nat) : Int) := by
  split
  · rw [show ((m:Rat)*(2:Rat)^e.toNat) = (((m*2^e.toNat:Nat):Int):Rat) by push_cast; rfl]
    exact Rat.floor_intCast _
  · exact floor_natCast_div_pow m (-e).toNat

/-- `truncRat` of a negated nonneg value: truncation toward zero of `-r` (`r ≥ 0`) is `-⌊r⌋`. -/
theorem truncRat_neg_of_nonneg {r : Rat} (hr : 0 ≤ r) : truncRat (-r) = -r.floor := by
  unfold truncRat
  split
  · rename_i h
    have h' : (-(0:Rat)) ≤ -r := by simpa using h
    have hr0 : r ≤ 0 := (Rat.neg_le_neg_iff).mp h'
    have : r = 0 := Rat.le_antisymm hr0 hr
    subst this
    norm_cast
  · rename_i h
    rw [Rat.ceil_eq_neg_floor_neg]
    simp

/-- `truncRat` (truncation toward zero) of the exact value a `finite` float denotes, expressed
via the same `mag` Nat that `Float.toInt` computes. -/
theorem truncRat_finiteToRat (neg : Bool) (m : Nat) (e : Int) :
    truncRat (finiteToRat neg m e) =
      if neg then -((if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat : Nat) : Int)
      else ((if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat : Nat) : Int) := by
  have hfloor := floor_magRat m e
  have hnn : (0:Rat) ≤
      (if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat) := by
    have h1 : (0:Rat) ≤
        (((if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)).floor
          : Rat) := by
      rw [hfloor]; exact_mod_cast Nat.zero_le _
    exact Rat.le_trans h1 (Rat.floor_le _)
  show truncRat
      (if neg then -(if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)
        else (if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)) = _
  cases neg with
  | false =>
    show truncRat (if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat) = _
    unfold truncRat
    rw [ite_eq_left hnn]
    exact hfloor
  | true =>
    show truncRat (-(if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat))
      = _
    rw [truncRat_neg_of_nonneg hnn]
    exact congrArg Neg.neg hfloor

/-- `@intFromFloat`, restated for the exact value `x` denotes: truncate `q = x.toRat?.get!`
toward zero, then range-check the same way `toInt_of_finite` does. -/
theorem toInt_of_toRat {s : Bool} {n : Nat} {safe : Bool} {x : Float fmt} {q : Rat}
    (hx : x.toRat? = some q) :
    Float.toInt s n safe x =
      let lo : Int := if s then -(2 ^ (n - 1) : Int) else 0
      let hi : Int := if s then (2 ^ (n - 1) : Int) - 1 else (2 ^ n : Int) - 1
      if truncRat q < lo || truncRat q > hi then
        if safe then throw .overflow else throw .unspecified
      else pure (BitVec.ofInt n (truncRat q)) := by
  obtain ⟨sn, m, e, hclass, hq⟩ := exists_finite_of_toRat? hx
  have htv : (if sn then -((if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat : Nat) : Int)
        else ((if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat : Nat) : Int))
      = truncRat q := by
    rw [← hq]; exact (truncRat_finiteToRat sn m e).symm
  rw [toInt_of_finite hclass]
  dsimp only
  rw [htv]

/-- `truncRat q` is negative iff `q ≤ -1` (truncation toward zero only crosses zero into the
negatives once the magnitude reaches a whole `1`). -/
theorem truncRat_lt_zero_iff {q : Rat} : truncRat q < 0 ↔ q ≤ -1 := by
  unfold truncRat
  split
  · rename_i h
    have hfl : (0:Int) ≤ q.floor := Rat.le_floor_iff.mpr (by exact_mod_cast h)
    constructor
    · intro hc; omega
    · intro hc; exact absurd (Rat.le_trans h hc) (by decide)
  · rename_i h
    have hnn : q < 0 := Rat.not_le.mp h
    constructor
    · intro hc
      have hc' : q.ceil ≤ (-1:Int) := by omega
      exact (Rat.ceil_le_iff.mp hc' : q ≤ ((-1:Int):Rat))
    · intro hc
      have : q.ceil ≤ (-1:Int) := Rat.ceil_le_iff.mpr (by exact_mod_cast hc)
      omega

/-- `truncRat q` exceeds a nonneg `n` iff `q ≥ n + 1` (the symmetric fact to
`truncRat_lt_zero_iff`, on the positive side). -/
theorem truncRat_gt_iff {q : Rat} {n : Int} (hn : 0 ≤ n) :
    truncRat q > n ↔ ((n:Rat) + 1) ≤ q := by
  unfold truncRat
  split
  · rename_i h
    constructor
    · intro hc
      have hstep : (n+1:Int) ≤ q.floor := by omega
      have := Rat.le_floor_iff.mp hstep
      push_cast at this
      exact this
    · intro hc
      have hc' : ((n+1:Int):Rat) ≤ q := by push_cast; exact hc
      have := Rat.le_floor_iff.mpr hc'
      omega
  · rename_i h
    have hnn : q < 0 := Rat.not_le.mp h
    have hceil0 : q.ceil ≤ (0:Int) := Rat.ceil_le_iff.mpr (by exact_mod_cast Rat.le_of_lt hnn)
    constructor
    · intro hc; omega
    · intro hc
      exfalso
      have h1 : (n:Rat) + 1 ≤ 0 := Rat.le_trans hc (Rat.le_of_lt hnn)
      have hn' : (0:Rat) ≤ (n:Rat) := by exact_mod_cast hn
      have h2 : (0:Rat) + 1 ≤ (n:Rat) + 1 := (Rat.add_le_add_right).mpr hn'
      have h3 : (1:Rat) ≤ 0 := by
        have h4 := Rat.le_trans h2 h1
        rwa [Rat.zero_add] at h4
      exact absurd h3 (by decide)

/-! ## Square root

`Float.sqrt`'s nonnegativity: a positive operand never produces NaN or a negative result. Built
from small classify/sign bridges (`sign_of_classify_*`), a mantissa bound reused from
`classify`'s bit layout (`classify_mantissa_lt`), a `Nat.sqrt` upper bound
(`sqrt_lt_of_lt_mul`), and the radicand bound that feeds it (`sqrt_shiftedM_lt`, mirroring
`sqrtCore`'s `te` clamp in `Ops.lean`). -/

/-- `classify`'s `inf` sign matches `signBit` (`signBit` is read off the raw bits; `classify`
recomputes it per format, so the two must agree for every format's `inf` encoding). -/
theorem sign_of_classify_inf {fmt : FloatFmt} {x : Float fmt} {s : Bool}
    (h : x.classify = .inf s) : s = x.signBit := by
  unfold Float.classify Float.signBit at *
  cases fmt <;> simp only [] at h <;>
    (split at h <;> (try split at h) <;> (try split at h)) <;> simp_all

/-- `classify`'s `finite` sign matches `signBit` (see `sign_of_classify_inf`). -/
theorem sign_of_classify_finite {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) : s = x.signBit := by
  unfold Float.classify Float.signBit at *
  cases fmt <;> simp only [] at h <;>
    (split at h <;> (try split at h) <;> (try split at h)) <;> simp_all

/-- `classify`'s mantissa always fits `fmt.prec` bits, for every format (subnormal or not: a
subnormal mantissa is the raw `frac` field, strictly under `2 ^ fracBits < 2 ^ prec`). -/
theorem classify_mantissa_lt {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) : m < 2 ^ fmt.prec := by
  have hpow : (2:Nat) ^ (fmt.fracBits + 1) = 2 ^ fmt.fracBits * 2 := Nat.pow_succ ..
  have hmod : x.bits.toNat % 2 ^ fmt.fracBits < 2 ^ fmt.fracBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  show m < 2 ^ (fmt.fracBits + 1)
  rw [hpow]
  unfold Float.classify at h
  cases fmt <;> simp only [] at h <;>
    (split at h <;> (try split at h) <;> (try split at h)) <;>
    (try injection h) <;> omega

/-- `finiteToRat`'s sign and mantissa, given its value is positive: the sign must be `false`
(a negative-sign value is `≤ 0`), and the mantissa nonzero (a zero mantissa denotes `0`). -/
theorem finiteToRat_sign_of_pos {s : Bool} {m : Nat} {e : Int} {q : Rat}
    (hq : finiteToRat s m e = q) (hpos : 0 < q) : s = false ∧ m ≠ 0 := by
  have hfloor := floor_magRat m e
  have hnn : (0:Rat) ≤
      (if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat) := by
    have h1 : (0:Rat) ≤
        (((if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)).floor
          : Rat) := by
      rw [hfloor]; exact_mod_cast Nat.zero_le _
    exact Rat.le_trans h1 (Rat.floor_le _)
  unfold finiteToRat at hq
  cases s with
  | true =>
    exfalso
    rw [← hq] at hpos
    have h2 : -(if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat) ≤ 0 := by
      have := Rat.neg_le_neg_iff.mpr hnn
      simpa using this
    simp only [ite_true] at hpos
    exact absurd hpos (Rat.not_lt.mpr h2)
  | false =>
    refine ⟨rfl, ?_⟩
    intro hm0
    subst hm0
    have hmag0 : (if e ≥ 0 then ((0:Nat):Rat) * (2:Rat)^e.toNat
        else ((0:Nat):Rat) / (2:Rat)^(-e).toNat) = 0 := by
      split
      · simp
      · show (0:Rat) * ((2:Rat) ^ (-e).toNat)⁻¹ = 0
        exact Rat.zero_mul _
    rw [hmag0] at hq
    rw [← hq] at hpos
    exact absurd hpos (by decide)

/-- `finiteToRat`'s magnitude, with a `false` sign, is always `≥ 0` (same `floor`/`Rat.floor_le`
argument as `finiteToRat_sign_of_pos`'s nonnegativity half, without the positivity hypothesis). -/
theorem finiteToRat_nonneg (m : Nat) (e : Int) : 0 ≤ finiteToRat false m e := by
  have hfloor := floor_magRat m e
  have h1 : (0:Rat) ≤
      (((if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)).floor
        : Rat) := by
    rw [hfloor]; exact_mod_cast Nat.zero_le _
  show (0:Rat) ≤ (if e ≥ 0 then (m:Rat) * (2:Rat)^e.toNat else (m:Rat) / (2:Rat)^(-e).toNat)
  exact Rat.le_trans h1 (Rat.floor_le _)

/-- `Float.add` preserves "not NaN and not negative": each of `nan`/`inf`/`finite` × `inf`/`finite`
combination either short-circuits to a non-negative `inf` (both signs are `false`, so `inf`'s
tie-break and the mixed cases all pick a `false`-signed side) or reduces to `roundRat_nonneg` once
`add`'s signed-zero special case is shown `false` (`finiteToRat_nonneg` on both summands rules out
the `sum < 0` disjunct; a `false` sign rules out the `-0 + -0 = -0` disjunct). -/
theorem add_nonneg {fmt : FloatFmt} {x y : Float fmt}
    (hxnan : x.isNaN = false) (hxsign : x.signBit = false)
    (hynan : y.isNaN = false) (hysign : y.signBit = false) :
    (Float.add x y).isNaN = false ∧ (Float.add x y).signBit = false := by
  unfold Float.add
  cases hcx : x.classify with
  | nan => exact absurd ((isNaN_iff x).mpr hcx) (by rw [hxnan]; decide)
  | inf sx =>
    have hsx : sx = false := (sign_of_classify_inf hcx).trans hxsign
    subst hsx
    cases hcy : y.classify with
    | nan => exact absurd ((isNaN_iff y).mpr hcy) (by rw [hynan]; decide)
    | inf sy =>
      have hsy : sy = false := (sign_of_classify_inf hcy).trans hysign
      subst hsy
      simp
    | finite sy my ey => simp
  | finite sx mx ex =>
    have hsx : sx = false := (sign_of_classify_finite hcx).trans hxsign
    subst hsx
    cases hcy : y.classify with
    | nan => exact absurd ((isNaN_iff y).mpr hcy) (by rw [hynan]; decide)
    | inf sy =>
      have hsy : sy = false := (sign_of_classify_inf hcy).trans hysign
      subst hsy
      simp
    | finite sy my ey =>
      have hsy : sy = false := (sign_of_classify_finite hcy).trans hysign
      subst hsy
      dsimp only
      have hnnx : 0 ≤ finiteToRat false mx ex := finiteToRat_nonneg mx ex
      have hnny : 0 ≤ finiteToRat false my ey := finiteToRat_nonneg my ey
      have hsum_nonneg : 0 ≤ finiteToRat false mx ex + finiteToRat false my ey :=
        Rat.add_nonneg hnnx hnny
      split
      · simp only [Bool.false_and]
        exact roundRat_nonneg fmt _
      · rw [decide_eq_false (Rat.not_lt.mpr hsum_nonneg)]
        exact roundRat_nonneg fmt _

/-- `x * x` is never NaN and never negative for a finite `x`, regardless of `x`'s own sign (the
product's sign is `s != s = false`). -/
theorem mul_self_nonneg {fmt : FloatFmt} {x : Float fmt} {s : Bool} {m : Nat} {e : Int}
    (hx : x.classify = .finite s m e) :
    (Float.mul x x).isNaN = false ∧ (Float.mul x x).signBit = false := by
  rw [mul_of_finite hx hx]
  have hs : (s != s) = false := by cases s <;> rfl
  rw [hs]
  exact roundRat_nonneg fmt _

/-- `Float.conv` preserves "not NaN and not negative" (no need for the operand's exact value:
the `finite` case reduces to `roundRat_nonneg`, the `inf` case to the `signBit`/`classify`
bridge above). -/
theorem conv_nonneg {fmt fmt2 : FloatFmt} {x : Float fmt}
    (hnan : x.isNaN = false) (hsign : x.signBit = false) :
    (Float.conv fmt2 x).isNaN = false ∧ (Float.conv fmt2 x).signBit = false := by
  unfold Float.conv
  cases hc : x.classify with
  | nan => exact absurd ((isNaN_iff x).mpr hc) (by rw [hnan]; decide)
  | inf s' =>
    have hs' : s' = x.signBit := sign_of_classify_inf hc
    rw [hs', hsign]
    simp
  | finite s' m' e' =>
    have hs' : s' = x.signBit := sign_of_classify_finite hc
    rw [hs', hsign]
    exact roundRat_nonneg fmt2 (finiteToRat false m' e')

/-- `Nat.sqrt`'s result stays under `k` whenever the radicand stays under `k * k` (no direct
upper-bound lemma for `Nat.sqrt` in core: derived from `Nat.sqrt_le`). -/
theorem sqrt_lt_of_lt_mul {n k : Nat} (h : n < k * k) : Nat.sqrt n < k := by
  by_cases hc : Nat.sqrt n < k
  · exact hc
  · exfalso
    have hge : k ≤ Nat.sqrt n := by omega
    have h1 : k * k ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hge hge
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    omega

/-- `sqrtCore`'s scaled radicand (`m <<< shiftAmt`, `shiftAmt = (e - 2 * te).toNat`) stays under
`2 ^ (2 * p)` whenever `te` sits in the window `sqrtCore` clamps it to (`hA`/`hC`, the same
bounds `Min.min`/`Max.max` enforce there). -/
theorem sqrt_shiftedM_lt {m : Nat} {p : Nat}
    {e te : Int} (hA : ((Nat.log2 m : Int) + e) / 2 - ((p:Int) - 1) ≤ te) (hC : te ≤ e / 2) :
    m <<< (e - 2 * te).toNat < 2 ^ (2 * p) := by
  have hshift_nonneg : 0 ≤ e - 2 * te := by omega
  have hshift_le : (e - 2*te).toNat ≤ 2*p - 1 - Nat.log2 m := by
    have h1 : e - 2*te ≤ 2*(p:Int) - 1 - (Nat.log2 m : Int) := by omega
    omega
  have hmlt : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  rw [Nat.shiftLeft_eq]
  calc m * 2 ^ (e - 2*te).toNat < 2 ^ (Nat.log2 m + 1) * 2 ^ (e - 2*te).toNat :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hmlt
    _ = 2 ^ (Nat.log2 m + 1 + (e - 2*te).toNat) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ (2*p) := Nat.pow_le_pow_right (by omega) (by omega)

/-- `sqrtCore` (`Float.sqrt`'s per-format worker) preserves "not NaN and not negative", given
the operand does: the `finite`/`m ≠ 0` case bounds the rounded mantissa via
`sqrt_shiftedM_lt` + `sqrt_lt_of_lt_mul`, then discharges `finalizeRounded_spec`'s hypothesis
exactly as `roundRat_m0_le` does for `roundRat`. -/
theorem sqrtCore_nonneg {fmt : FloatFmt} {y : Float fmt}
    (hnan : y.isNaN = false) (hsign : y.signBit = false) :
    (Float.sqrt.sqrtCore fmt y).isNaN = false ∧ (Float.sqrt.sqrtCore fmt y).signBit = false := by
  unfold Float.sqrt.sqrtCore
  cases hc : y.classify with
  | nan => exact absurd ((isNaN_iff y).mpr hc) (by rw [hnan]; decide)
  | inf s' =>
    have hs' : s' = false := (sign_of_classify_inf hc).trans hsign
    subst hs'
    simp
  | finite s' m' e' =>
    have hs' : s' = false := (sign_of_classify_finite hc).trans hsign
    subst hs'
    dsimp only
    by_cases hm0 : m' = 0
    · rw [ite_eq_left hm0]
      exact ⟨isNaN_zero false, signBit_zero false⟩
    · rw [ite_eq_right hm0]
      have hmlt : m' < 2 ^ fmt.prec := classify_mantissa_lt hc
      have hp1 : 1 ≤ fmt.prec := by cases fmt <;> decide
      have hlog : (Nat.log2 m' : Int) < (fmt.prec:Int) := by
        exact_mod_cast (Nat.log2_lt hm0).mpr hmlt
      have hexle : (Nat.log2 m' : Int) + e' ≤ e' + ((fmt.prec:Int) - 1) := by omega
      apply finalizeRounded_spec
      have hediv2 : ∀ x : Int, x.ediv 2 = x / 2 := fun _ => rfl
      simp only [hediv2]
      have hA : ((Nat.log2 m':Int)+e')/2 - ((fmt.prec:Int)-1) ≤
          Min.min (Max.max (((Nat.log2 m':Int)+e')/2 - ((fmt.prec:Int)-1))
            (fmt.emin-((fmt.prec:Int)-1))) (e'/2) := by omega
      have hC : Min.min (Max.max (((Nat.log2 m':Int)+e')/2 - ((fmt.prec:Int)-1))
          (fmt.emin-((fmt.prec:Int)-1))) (e'/2) ≤ e'/2 := by omega
      have hshiftedM_lt := sqrt_shiftedM_lt hA hC
      have h2p : (2:Nat)^(2*fmt.prec) = 2^fmt.prec * 2^fmt.prec := by
        rw [Nat.two_mul, Nat.pow_add]
      have hrootlt : Nat.sqrt (m' <<< (e' - 2 *
          (Min.min (Max.max (((Nat.log2 m':Int)+e')/2 - ((fmt.prec:Int)-1))
            (fmt.emin-((fmt.prec:Int)-1))) (e'/2))).toNat) < 2 ^ fmt.prec := by
        apply sqrt_lt_of_lt_mul
        rw [← h2p]
        exact hshiftedM_lt
      have hcast : ((2:Nat) ^ fmt.prec : Int) = (2 : Int) ^ fmt.prec := by exact_mod_cast rfl
      split <;> omega

/-- `Float.sqrt` preserves "not NaN and not negative", for any operand (not just a positive one:
`0` and `+inf` both take the same path). `f128` double-rounds through `f64` (`Ops.lean`'s special
case): `conv_nonneg` wraps each `Float.conv`, and `sqrtCore_nonneg` (general in operand sign)
handles both the direct path and the inner `f64` step. -/
theorem sqrt_nonneg_of_sign {fmt : FloatFmt} {x : Float fmt}
    (hnan : x.isNaN = false) (hsign : x.signBit = false) :
    (Float.sqrt x).isNaN = false ∧ (Float.sqrt x).signBit = false := by
  by_cases hfmt : fmt = .f128
  · subst hfmt
    unfold Float.sqrt
    rw [dite_eq_left rfl]
    have hinner := conv_nonneg (fmt2 := .f64) hnan hsign
    have hcore := sqrtCore_nonneg hinner.1 hinner.2
    exact conv_nonneg hcore.1 hcore.2
  · unfold Float.sqrt
    rw [dite_eq_right hfmt]
    exact sqrtCore_nonneg hnan hsign

/-- `Float.sqrt` of a positive operand is never NaN and never negative (`sqrt_nonneg_of_sign`,
specialized to a `toRat?`-positive operand). -/
theorem sqrt_nonneg {fmt : FloatFmt} {x : Float fmt} {q : Rat}
    (hx : x.toRat? = some q) (hq : 0 < q) :
    (Float.sqrt x).isNaN = false ∧ (Float.sqrt x).signBit = false := by
  obtain ⟨s, m, e, hc, hfr⟩ := exists_finite_of_toRat? hx
  obtain ⟨hs, _⟩ := finiteToRat_sign_of_pos hfr hq
  subst hs
  have hxnan : x.isNaN = false := by unfold Float.isNaN; rw [hc]
  have hxsign : x.signBit = false := (sign_of_classify_finite hc).symm
  exact sqrt_nonneg_of_sign hxnan hxsign

end Zig
