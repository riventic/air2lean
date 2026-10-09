import ZigLean.Float.Lemmas

/-!
# Allowed float results (target variation)

The model is deterministic: where Zig leaves a float result to the target, it picks one
(`docs/floats.md` §NaN, §+0 and −0). A proof about generated code should not depend on that
choice. This file states the set of results the target may produce instead, and the lemmas a
proof needs to show that a property holds for every one of them (`docs/floats.md`
§Allowed results):

* `Float.Allowed x r`: the target may return `r` where the model returns `x`. `x` not NaN:
  only `r = x`, bit for bit (incl. an f80 pseudo-denormal's encoding and the sign of a zero).
  `x` NaN: any NaN — sign, payload and, for f80, encoding (incl. unnormals and pseudo-NaNs)
  are unconstrained.
* `Float.MinAllowed`/`Float.MaxAllowed`: f32/f64 `@min`/`@max` of `+0` and `−0` (group D)
  may give either zero; a signaling NaN and a non-NaN (group I) may give the non-NaN operand
  or a NaN; otherwise `Float.Allowed` of the model's result.
* `Float.AllowedSpec c P`: `c` succeeds, and `P` holds for every allowed result.

Errors are not variation. An illegal input (`@intFromFloat` out of range: `.overflow` with the
safety check, `.illegal` for a NaN or without the check) stays a `throw` for every allowed
operand (`Float.toInt_allowed`).
-/

namespace Zig

variable {fmt : FloatFmt}

/-! ## The relation -/

/-- The target may return `r` where the model returns `x`: `x` itself, or any NaN when `x` is
a NaN (Zig leaves a NaN's sign and payload unspecified). -/
def Float.Allowed (x r : Float fmt) : Prop :=
  if x.isNaN then r.isNaN = true else r = x

/-- The model's own result is allowed. -/
theorem Float.Allowed.refl (x : Float fmt) : Float.Allowed x x := by
  unfold Float.Allowed; split <;> simp_all

/-- An allowed result of a non-NaN model result is that result. -/
theorem Float.Allowed.eq_of_not_isNaN {x r : Float fmt} (h : Float.Allowed x r)
    (hx : x.isNaN = false) : r = x := by
  unfold Float.Allowed at h; simp_all

/-- Every allowed result of a NaN model result is a NaN. -/
theorem Float.Allowed.isNaN_of_isNaN {x r : Float fmt} (h : Float.Allowed x r)
    (hx : x.isNaN = true) : r.isNaN = true := by
  unfold Float.Allowed at h; simp_all

/-- Any two NaNs are allowed results of each other: the relation does not see the payload. -/
theorem Float.Allowed.of_isNaN {x r : Float fmt} (hx : x.isNaN = true) (hr : r.isNaN = true) :
    Float.Allowed x r := by
  unfold Float.Allowed; simp_all

/-- Allowed results classify alike: every op that reads its operand only through `classify`
gives the same result on all of them. -/
theorem Float.Allowed.classify_eq {x r : Float fmt} (h : Float.Allowed x r) :
    r.classify = x.classify := by
  cases hx : x.isNaN
  · rw [h.eq_of_not_isNaN hx]
  · rw [(isNaN_iff r).mp (h.isNaN_of_isNaN hx), (isNaN_iff x).mp hx]

theorem Float.Allowed.isNaN_eq {x r : Float fmt} (h : Float.Allowed x r) : r.isNaN = x.isNaN := by
  unfold Float.isNaN; rw [h.classify_eq]

theorem Float.Allowed.toRat?_eq {x r : Float fmt} (h : Float.Allowed x r) : r.toRat? = x.toRat? := by
  unfold Float.toRat?; rw [h.classify_eq]

/-! ## Payload independence

Comparisons and arithmetic do not observe which allowed result an operand is: the outcome is
the same, or (for a NaN-producing op) again an allowed result. -/

theorem Float.Allowed.lt_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.lt a' b' = Float.lt a b := by
  unfold Float.lt; rw [ha.classify_eq, hb.classify_eq]

theorem Float.Allowed.eq_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.eq a' b' = Float.eq a b := by
  unfold Float.eq; rw [ha.classify_eq, hb.classify_eq]

theorem Float.Allowed.le_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.le a' b' = Float.le a b := by
  unfold Float.le; rw [ha.lt_eq hb, ha.eq_eq hb]

theorem Float.Allowed.ne_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.ne a' b' = Float.ne a b := by
  unfold Float.ne; rw [ha.eq_eq hb]

theorem Float.Allowed.gt_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.gt a' b' = Float.gt a b := hb.lt_eq ha

theorem Float.Allowed.ge_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.ge a' b' = Float.ge a b := hb.le_eq ha

/-- `+`, `*`, `/` read their operands only through `classify` (a NaN operand gives the
canonical NaN), so allowed operands give the model's result exactly. -/
theorem Float.Allowed.add_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.add a' b' = Float.add a b := by
  unfold Float.add; rw [ha.classify_eq, hb.classify_eq]

theorem Float.Allowed.mul_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.mul a' b' = Float.mul a b := by
  unfold Float.mul; rw [ha.classify_eq, hb.classify_eq]

theorem Float.Allowed.div_eq {a a' b b' : Float fmt} (ha : Float.Allowed a a')
    (hb : Float.Allowed b b') : Float.div a' b' = Float.div a b := by
  unfold Float.div; rw [ha.classify_eq, hb.classify_eq]

theorem Float.Allowed.sqrt_eq {a a' : Float fmt} (ha : Float.Allowed a a') :
    Float.sqrt a' = Float.sqrt a := by
  unfold Float.sqrt Float.sqrt.sqrtCore; rw [ha.classify_eq]

theorem Float.Allowed.conv_eq (fmt2 : FloatFmt) {a a' : Float fmt} (ha : Float.Allowed a a') :
    Float.conv fmt2 a' = Float.conv fmt2 a := by
  unfold Float.conv; rw [ha.classify_eq]

/-! ## Errors stay errors -/

/-- `@intFromFloat` gives the same outcome on every allowed operand, so an illegal input
(`.overflow`: out of range, or ±inf, with the safety check; `.illegal`: NaN of any payload,
which the check misses) is a `throw` for each of them, never absorbed into the variation. -/
theorem Float.toInt_allowed (s : Bool) (n : Nat) (safe : Bool) {x r : Float fmt}
    (h : Float.Allowed x r) : Float.toInt s n safe r = Float.toInt s n safe x := by
  unfold Float.toInt; rw [h.classify_eq]

/-! ## Signed zero of f32/f64 `@min`/`@max` (group D) -/

/-- The operands are `+0` and `−0` (either order) in a format whose `@min`/`@max` returns a
target-dependent zero (f32/f64, `docs/floats.md` §+0 and −0). Exactly where `Float.minChk`
and `Float.maxChk` throw `.unspecified`. -/
def Float.zeroSignVaries (a b : Float fmt) : Bool :=
  match a.classify, b.classify with
  | .finite sa 0 _, .finite sb 0 _ =>
    match fmt with
    | .f32 | .f64 => sa != sb
    | .f16 | .f80 | .f128 => false
  | _, _ => false

/-- The results the target may give for `@min(a, b)`: either zero in the group D case; in the
group I case (`Float.snanVaries`), the non-NaN operand (`Float.min a b`) or any NaN; otherwise
the allowed results of `Float.min a b`. -/
def Float.MinAllowed (a b r : Float fmt) : Prop :=
  if Float.zeroSignVaries a b then r = Float.zero false ∨ r = Float.zero true
  else if Float.snanVaries a b then Float.Allowed (Float.min a b) r ∨ r.isNaN = true
  else Float.Allowed (Float.min a b) r

/-- `@max`'s allowed results: as `Float.MinAllowed`. -/
def Float.MaxAllowed (a b r : Float fmt) : Prop :=
  if Float.zeroSignVaries a b then r = Float.zero false ∨ r = Float.zero true
  else if Float.snanVaries a b then Float.Allowed (Float.max a b) r ∨ r.isNaN = true
  else Float.Allowed (Float.max a b) r

theorem Float.minChk_eq (a b : Float fmt) : Float.minChk a b =
    if Float.zeroSignVaries a b || Float.snanVaries a b then throw .unspecified
    else pure (Float.min a b) := by
  unfold Float.minChk
  by_cases hs : Float.snanVaries a b = true
  · simp [hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    unfold Float.zeroSignVaries
    generalize a.classify = ca; generalize b.classify = cb
    rcases ca with _ | _ | ⟨sa, _ | _, _⟩ <;> rcases cb with _ | _ | ⟨sb, _ | _, _⟩ <;>
      cases fmt <;> simp

theorem Float.maxChk_eq (a b : Float fmt) : Float.maxChk a b =
    if Float.zeroSignVaries a b || Float.snanVaries a b then throw .unspecified
    else pure (Float.max a b) := by
  unfold Float.maxChk
  by_cases hs : Float.snanVaries a b = true
  · simp [hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    unfold Float.zeroSignVaries
    generalize a.classify = ca; generalize b.classify = cb
    rcases ca with _ | _ | ⟨sa, _ | _, _⟩ <;> rcases cb with _ | _ | ⟨sb, _ | _, _⟩ <;>
      cases fmt <;> simp

/-- The group D operands are two zeros, and `Float.min`/`Float.max` return a zero for them. -/
private theorem zeroSignVaries_spec {a b : Float fmt} (h : Float.zeroSignVaries a b = true) :
    (Float.min a b = Float.zero false ∨ Float.min a b = Float.zero true) ∧
    (Float.max a b = Float.zero false ∨ Float.max a b = Float.zero true) := by
  unfold Float.zeroSignVaries at h
  unfold Float.min Float.max
  split at h
  · rename_i sa ea sb eb hca hcb
    rw [hca, hcb]
    cases fmt <;> simp at h ⊢ <;> cases sa <;> cases sb <;> simp
  · simp at h

/-- Soundness of the checked model: whenever `Float.minChk` returns a value, it is allowed. -/
theorem Float.minChk_allowed {a b v : Float fmt} (h : Float.minChk a b = pure v) :
    Float.MinAllowed a b v := by
  rw [Float.minChk_eq] at h
  unfold Float.MinAllowed
  split at h
  · cases h
  · rename_i hv
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hv
    simp only [hv.1, hv.2, Bool.false_eq_true, ↓reduceIte]
    have : v = Float.min a b := by injection h with h; injection h with h; exact h.symm
    subst this; exact Float.Allowed.refl _

theorem Float.maxChk_allowed {a b v : Float fmt} (h : Float.maxChk a b = pure v) :
    Float.MaxAllowed a b v := by
  rw [Float.maxChk_eq] at h
  unfold Float.MaxAllowed
  split at h
  · cases h
  · rename_i hv
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hv
    simp only [hv.1, hv.2, Bool.false_eq_true, ↓reduceIte]
    have : v = Float.max a b := by injection h with h; injection h with h; exact h.symm
    subst this; exact Float.Allowed.refl _

/-- Soundness of the total model: `Float.min`'s deterministic default is allowed, also in the
group D case that `Float.minChk` refuses. -/
theorem Float.min_allowed (a b : Float fmt) : Float.MinAllowed a b (Float.min a b) := by
  unfold Float.MinAllowed
  split
  · rename_i h; exact (zeroSignVaries_spec h).1
  · split
    · exact .inl (Float.Allowed.refl _)
    · exact Float.Allowed.refl _

theorem Float.max_allowed (a b : Float fmt) : Float.MaxAllowed a b (Float.max a b) := by
  unfold Float.MaxAllowed
  split
  · rename_i h; exact (zeroSignVaries_spec h).2
  · split
    · exact .inl (Float.Allowed.refl _)
    · exact Float.Allowed.refl _

/-- A signed zero classifies as a finite value with mantissa 0. -/
theorem Float.classify_zero (neg : Bool) :
    (Float.zero (fmt := fmt) neg).classify = .finite neg 0 (fmt.emin - fmt.fracBits) := by
  cases fmt <;> cases neg <;> decide

/-- Both zeros compare equal to `+0` and are not NaN. -/
private theorem zero_eq_zero (neg : Bool) :
    Float.eq (Float.zero (fmt := fmt) neg) (Float.zero false) = true ∧
      (Float.zero (fmt := fmt) neg).isNaN = false := by
  refine ⟨?_, isNaN_zero neg⟩
  unfold Float.eq
  rw [Float.classify_zero, Float.classify_zero]
  cases neg <;> simp [finiteToRat, Rat.div_def]

/-- In the group D case, every allowed `@min`/`@max` result compares equal to `+0` and is not
NaN, whichever zero the target picks. -/
theorem Float.MinAllowed.eq_zero {a b r : Float fmt} (hv : Float.zeroSignVaries a b = true)
    (h : Float.MinAllowed a b r) : Float.eq r (Float.zero false) = true ∧ r.isNaN = false := by
  unfold Float.MinAllowed at h
  simp only [hv, ite_true] at h
  rcases h with rfl | rfl <;> exact zero_eq_zero _

theorem Float.MaxAllowed.eq_zero {a b r : Float fmt} (hv : Float.zeroSignVaries a b = true)
    (h : Float.MaxAllowed a b r) : Float.eq r (Float.zero false) = true ∧ r.isNaN = false := by
  unfold Float.MaxAllowed at h
  simp only [hv, ite_true] at h
  rcases h with rfl | rfl <;> exact zero_eq_zero _

/-! ## Lifted spec form -/

/-- `c` succeeds, and `P` holds for every result the target may return in place of the
model's: the form a proof states about a float result that may vary by target. A failing `c`
(illegal behavior or an unspecified case) satisfies no `AllowedSpec`. -/
def Float.AllowedSpec (c : Result (Float fmt)) (P : Float fmt → Prop) : Prop :=
  ∃ x, c = pure x ∧ ∀ r, Float.Allowed x r → P r

/-- An `AllowedSpec` covers the model's own result. -/
theorem Float.AllowedSpec.model {c : Result (Float fmt)} {P : Float fmt → Prop}
    (h : Float.AllowedSpec c P) : ∃ x, c = pure x ∧ P x :=
  let ⟨x, hc, hp⟩ := h; ⟨x, hc, hp x (Float.Allowed.refl x)⟩

/-- A failing computation satisfies no `AllowedSpec`. -/
theorem Float.AllowedSpec.not_throw {e : Error} {P : Float fmt → Prop} :
    ¬ Float.AllowedSpec (throw e) P := by
  rintro ⟨x, hc, -⟩; cases hc

/-- A property that reads its argument only through `classify` holds for every allowed result
iff it holds for the model's. -/
theorem Float.allowedSpec_pure_of_classify {x : Float fmt} {P : Float fmt → Prop}
    (hP : ∀ y z : Float fmt, y.classify = z.classify → P y → P z) (hx : P x) :
    Float.AllowedSpec (pure x) P :=
  ⟨x, rfl, fun _ h => hP x _ h.classify_eq.symm hx⟩

end Zig
