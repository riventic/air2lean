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

end Zig
