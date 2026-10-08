import ZigLean.Float.Error
import Proofs.Floats.Dot

/-!
# Numerical bounds for `fitness` (`examples/floats/floats.zig`)

`fitness(xs, ws, target, penalty)` scores a candidate: from `s = +0` it accumulates, in loop
order, `s += w * x - penalty * (d * d)` with `d = x - target`, a weighted sum with a
squared-deviation penalty. Every term takes five roundings (`-`, `*`, `*`, `*`, `-`) before it
is added. `fitness_eq_sumLeft` turns the generated loop into the left fold `Zig.Float.sumLeft`
of the rounded terms `fitTerm`, in loop order.

The stated property (`fitness_error`): with inputs `|xᵢ|, |target| ≤ B`, `|wᵢ| ≤ W`,
`|penalty| ≤ P` and the overflow preconditions `2B < 2^1023`, `D² < 2^1023` and
`n·(T + η)·ρⁿ < 2^1023` (`D`, `T` below; `ρ = 1 + u`, `u = 2^-53`, `η = 2^-1075`), the result
is finite (no NaN, no infinity, no panic), of magnitude at most `n·(T + η)·ρⁿ`, and within
`n·(u·n·(T + η)·ρⁿ + η) + n·E` of the exact fitness `∑ (wᵢ·xᵢ - penalty·(xᵢ - target)²)`.
`fitness_isNaN` is the NaN condition, `fitness_gt_of_gap` a stable comparison against a
threshold and `fitness_panic` the length-mismatch panic.

The per-term bounds (`fitTermBound` = `T`, `fitTermErr` = `E`) follow the five roundings:

| step | exact | magnitude bound | rounding error |
|---|---|---|---|
| `d = x - target` | `δ = x - target`, `|δ| ≤ 2B` | `D = 2B + e₁` | `e₁ = u·2B + η` |
| `d * d` | `d·d`, `≤ D²` | `Q = D² + e₂` | `e₂ = u·D² + η` |
| `penalty * (d * d)` | `≤ P·Q` | `R = P·Q + e₃` | `e₃ = u·P·Q + η` |
| `w * x` | `≤ W·B` | `X = W·B + e₄` | `e₄ = u·W·B + η` |
| `w * x - penalty * (d * d)` | `≤ X + R` | `T = X + R + e₅` | `e₅ = u·(X + R) + η` |

and `E = e₅ + e₄ + e₃ + P·(e₂ + e₁·(D + 2B))`: the last term propagates the error of `d` through
the square (`|d·d - δ²| ≤ e₁·(D + 2B)`) and the penalty factor.

The proofs follow the loop's evaluation order; none reassociates a float sum.
-/

open Floats

local notation "u64" => Zig.FloatFmt.f64.unitRoundoff
local notation "η64" => Zig.FloatFmt.f64.underflowError
local notation "Ω64" => Zig.FloatFmt.f64.overflowBound

/-! ## Per-term bounds -/

/-- `e₁`: rounding error of `d = x - target`. -/
def fitE1 (B : Rat) : Rat := u64 * (2 * B) + η64
/-- `D`: magnitude bound of `d`. -/
def fitD (B : Rat) : Rat := 2 * B + fitE1 B
/-- `e₂`: rounding error of `d * d`. -/
def fitE2 (B : Rat) : Rat := u64 * (fitD B * fitD B) + η64
/-- `Q`: magnitude bound of `d * d`. -/
def fitQ (B : Rat) : Rat := fitD B * fitD B + fitE2 B
/-- `e₃`: rounding error of `penalty * (d * d)`. -/
def fitE3 (B P : Rat) : Rat := u64 * (P * fitQ B) + η64
/-- `R`: magnitude bound of `penalty * (d * d)`. -/
def fitR (B P : Rat) : Rat := P * fitQ B + fitE3 B P
/-- `e₄`: rounding error of `w * x`. -/
def fitE4 (B W : Rat) : Rat := u64 * (W * B) + η64
/-- `X`: magnitude bound of `w * x`. -/
def fitX (B W : Rat) : Rat := W * B + fitE4 B W
/-- `e₅`: rounding error of the term's final `-`. -/
def fitE5 (B W P : Rat) : Rat := u64 * (fitX B W + fitR B P) + η64
/-- `T`: magnitude bound of a rounded term. -/
def fitTermBound (B W P : Rat) : Rat := fitX B W + fitR B P + fitE5 B W P
/-- `E`: distance of a rounded term from its exact value `w·x - penalty·(x - target)²`. -/
def fitTermErr (B W P : Rat) : Rat :=
  fitE5 B W P + fitE4 B W + fitE3 B P + P * (fitE2 B + fitE1 B * (fitD B + 2 * B))

/-- The `i`-th rounded term `w * x - penalty * (d * d)`, `d = x - target`, in the generated
code's operation order. -/
def fitTerm (xs ws : Array Zig.F64) (target penalty : Zig.F64) (i : Nat) : Zig.F64 :=
  let d := Zig.Float.sub xs[i]! target
  Zig.Float.sub (Zig.Float.mul ws[i]! xs[i]!) (Zig.Float.mul penalty (Zig.Float.mul d d))

/-- The loop's partial sum after `k` iterations. -/
def fitAcc (xs ws : Array Zig.F64) (target penalty : Zig.F64) (k : Nat) : Zig.F64 :=
  Zig.Float.sumLeft (Zig.Float.ofBits (0 : BitVec 64)) (fitTerm xs ws target penalty) k

/-! ## The loop is a left fold -/

theorem fitness_loop_step (xs ws : Array Zig.F64) (target penalty : Zig.F64)
    (hs : xs.size < 2 ^ 64) (hlen : xs.size = ws.size) (s : fitnessLocals)
    (hk : s.local6.toNat ≤ xs.size) (ht : s.s = fitAcc xs ws target penalty s.local6.toNat) :
    ∃ e s', (fitness.loop17 xs ws target penalty (Zig.len xs)).run s = pure (e, s') ∧
      (if fitness.again17 e then
          (s'.local6.toNat ≤ xs.size ∧ s'.s = fitAcc xs ws target penalty s'.local6.toNat) ∧
            xs.size - s'.local6.toNat < xs.size - s.local6.toNat
        else e = .br16 ∧ s'.s = fitAcc xs ws target penalty xs.size) := by
  unfold fitness.loop17
  have hm : xs.size % 18446744073709551616 = xs.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : s.local6.toNat < xs.size
  · have hlt' : s.local6.toNat < ws.size := hlen ▸ hlt
    have hinc : ¬ 18446744073709551615 ≤ s.local6.toNat := by omega
    refine ⟨.rep17, ⟨Zig.Float.add s.s
      (Zig.Float.sub (Zig.Float.mul (ws[s.local6.toNat]'hlt') (xs[s.local6.toNat]'hlt))
        (Zig.Float.mul penalty
          (Zig.Float.mul (Zig.Float.sub (xs[s.local6.toNat]'hlt) target)
            (Zig.Float.sub (xs[s.local6.toNat]'hlt) target)))), s.local6 + 1⟩, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hlt', hm, hinc, StateT.lift]
    · have h5 : (s.local6 + 1).toNat = s.local6.toNat + 1 := Zig.toNat_add_one _ (by omega)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h5]; omega
      · rw [h5, ht]
        simp [fitAcc, Zig.Float.sumLeft, fitTerm, hlt, hlt']
      · rw [h5]; omega
  · have heq : s.local6.toNat = xs.size := by omega
    refine ⟨.br16, s, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm]
    · simp only [fitness.again17, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, heq ▸ ht⟩

/-- `fitness` of two equal-length slices is the left fold of the rounded terms from `+0`, in
loop order. -/
theorem fitness_eq_sumLeft (xs ws : Array Zig.F64) (target penalty : Zig.F64)
    (hs : xs.size < 2 ^ 64) (hlen : xs.size = ws.size) :
    fitness xs ws target penalty = pure (fitAcc xs ws target penalty xs.size) := by
  obtain ⟨⟨e, s'⟩, hrun, he, hpost⟩ := Zig.loop_spec
    (fitness.loop17 xs ws target penalty (Zig.len xs)) fitness.again17
    (fun s => s.local6.toNat ≤ xs.size ∧ s.s = fitAcc xs ws target penalty s.local6.toNat)
    (fun s => xs.size - s.local6.toNat)
    (fun r => r.1 = .br16 ∧ r.2.s = fitAcc xs ws target penalty xs.size)
    (fun s hs' => fitness_loop_step xs ws target penalty hs hlen s hs'.1 hs'.2)
    { s := Zig.Float.ofBits (0 : BitVec 64), local6 := 0 }
    (by simp [fitAcc, Zig.Float.sumLeft])
  subst he
  have hne : (Zig.len xs = Zig.len ws) = True := eq_true (by simp [Zig.len, hlen])
  unfold fitness
  change Zig.loop (fitness.loop17 xs ws target penalty (Zig.len xs)) fitness.again17
    { s := Zig.Float.ofBits 0#64, local6 := 0#64 } = some (Except.ok (fitnessExit.br16, s'))
    at hrun
  simp only at hpost
  simp [zig_unfold, hne, StateT.bind, hrun, hpost]

/-- **Panic condition.** Slices of different lengths panic (`for (xs, ws)` checks them). -/
theorem fitness_panic (xs ws : Array Zig.F64) (target penalty : Zig.F64)
    (hxs : xs.size < 2 ^ 64) (hws : ws.size < 2 ^ 64) (hlen : xs.size ≠ ws.size) :
    fitness xs ws target penalty = throw .panic := by
  have hne : (Zig.len xs = Zig.len ws) = False := eq_false (by
    simp only [Zig.len]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hxs, Nat.mod_eq_of_lt hws] at this
    exact hlen this)
  unfold fitness
  simp [zig_unfold, hne, StateT.bind]

/-! ## One term -/

/-- One rounded term of `fitness`: finite, within `E` of the exact `w·x - p·(x - t)²` and of
magnitude at most `T`, under the per-step overflow preconditions. -/
theorem fitTerm_error (xs ws : Array Zig.F64) (target penalty : Zig.F64) {i : Nat}
    (hi : i < xs.size) (hi' : i < ws.size) {x w t p B W P : Rat} (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hP : 0 ≤ P) (hx : xs[i].toRat? = some x ∧ -B ≤ x ∧ x ≤ B)
    (hw : ws[i].toRat? = some w ∧ -W ≤ w ∧ w ≤ W)
    (ht : target.toRat? = some t ∧ -B ≤ t ∧ t ≤ B)
    (hp : penalty.toRat? = some p ∧ -P ≤ p ∧ p ≤ P)
    (hov2B : 2 * B < Ω64) (hovD : fitD B * fitD B < Ω64) (hovT : fitTermBound B W P < Ω64) :
    ∃ v, (fitTerm xs ws target penalty i).toRat? = some v ∧
      v - (w * x - p * ((x - t) * (x - t))) ≤ fitTermErr B W P ∧
      (w * x - p * ((x - t) * (x - t))) - v ≤ fitTermErr B W P ∧
      -fitTermBound B W P ≤ v ∧ v ≤ fitTermBound B W P := by
  have hu := Rat.le_of_lt (Zig.FloatFmt.unitRoundoff_pos .f64)
  have hη := Rat.le_of_lt (Zig.FloatFmt.underflowError_pos .f64)
  -- Nonnegative bounds.
  have he1 : 0 ≤ fitE1 B := by
    have := Rat.mul_nonneg hu (show 0 ≤ 2 * B by grind); unfold fitE1; grind
  have hD : 0 ≤ fitD B := by unfold fitD; grind
  have hDD := Rat.mul_nonneg hD hD
  have he2 : 0 ≤ fitE2 B := by have := Rat.mul_nonneg hu hDD; unfold fitE2; grind
  have hQ : 0 ≤ fitQ B := by unfold fitQ; grind
  have hPQ := Rat.mul_nonneg hP hQ
  have he3 : 0 ≤ fitE3 B P := by have := Rat.mul_nonneg hu hPQ; unfold fitE3; grind
  have hR : 0 ≤ fitR B P := by unfold fitR; grind
  have hWB := Rat.mul_nonneg hW hB
  have he4 : 0 ≤ fitE4 B W := by have := Rat.mul_nonneg hu hWB; unfold fitE4; grind
  have hX : 0 ≤ fitX B W := by unfold fitX; grind
  have he5 : 0 ≤ fitE5 B W P := by
    have := Rat.mul_nonneg hu (show 0 ≤ fitX B W + fitR B P by grind); unfold fitE5; grind
  have hTR : fitR B P ≤ fitTermBound B W P := by unfold fitTermBound; grind
  have hTX : fitX B W ≤ fitTermBound B W P := by unfold fitTermBound; grind
  have hPQR : P * fitQ B ≤ fitR B P := by unfold fitR; grind
  have hWBX : W * B ≤ fitX B W := by unfold fitX; grind
  have hXR : fitX B W + fitR B P ≤ fitTermBound B W P := by unfold fitTermBound; grind
  -- `d = x - target`.
  obtain ⟨d, hd, d1, d2⟩ := Zig.sub_error hx.1 ht.1 (A := 2 * B) (by grind) (by grind) hov2B
  have hdD : -fitD B ≤ d ∧ d ≤ fitD B := by unfold fitD fitE1; constructor <;> grind
  -- `d * d`.
  obtain ⟨q1, q2⟩ := Zig.mul_abs_le hdD hdD
  obtain ⟨q, hq, e21, e22⟩ := Zig.mul_error hd hd q1 q2 hovD
  have hqQ : -fitQ B ≤ q ∧ q ≤ fitQ B := by unfold fitQ fitE2; constructor <;> grind
  -- `penalty * (d * d)`.
  obtain ⟨r1, r2⟩ := Zig.mul_abs_le (⟨hp.2.1, hp.2.2⟩ : -P ≤ p ∧ p ≤ P) hqQ
  obtain ⟨r, hr, e31, e32⟩ := Zig.mul_error hp.1 hq r1 r2 (by grind)
  have hrR : -fitR B P ≤ r ∧ r ≤ fitR B P := by unfold fitR fitE3; constructor <;> grind
  -- `w * x`.
  obtain ⟨m1, m2⟩ := Zig.mul_abs_le (⟨hw.2.1, hw.2.2⟩ : -W ≤ w ∧ w ≤ W)
    (⟨hx.2.1, hx.2.2⟩ : -B ≤ x ∧ x ≤ B)
  obtain ⟨m, hm, e41, e42⟩ := Zig.mul_error hw.1 hx.1 m1 m2 (by grind)
  have hmX : -fitX B W ≤ m ∧ m ≤ fitX B W := by unfold fitX fitE4; constructor <;> grind
  -- The term `w * x - penalty * (d * d)`.
  obtain ⟨v, hv, e51, e52⟩ := Zig.sub_error hm hr (A := fitX B W + fitR B P) (by grind)
    (by grind) (by grind)
  refine ⟨v, ?_, ?_⟩
  · simp only [fitTerm, getElem!_pos xs i hi, getElem!_pos ws i hi']
    exact hv
  -- Propagate `d`'s error through the square and the penalty factor.
  have hδ : -(2 * B) ≤ x - t ∧ x - t ≤ 2 * B := by constructor <;> grind
  obtain ⟨s1, s2⟩ := Zig.mul_sub_mul_le hdD hδ (b := d) (a' := x - t) (δa := fitE1 B) (δb := fitE1 B)
    (by unfold fitE1; constructor <;> grind) (by unfold fitE1; constructor <;> grind)
  have hqδ : -(fitE2 B + fitE1 B * (fitD B + 2 * B)) ≤ q - (x - t) * (x - t) ∧
      q - (x - t) * (x - t) ≤ fitE2 B + fitE1 B * (fitD B + 2 * B) := by
    unfold fitE2 at *; constructor <;> grind
  obtain ⟨b1, b2⟩ := Zig.mul_abs_le hδ hδ
  obtain ⟨p1, p2⟩ := Zig.mul_sub_mul_le (⟨hp.2.1, hp.2.2⟩ : -P ≤ p ∧ p ≤ P) ⟨b1, b2⟩
    (b := q) (a' := p) (δa := 0) (δb := fitE2 B + fitE1 B * (fitD B + 2 * B)) (by grind) hqδ
  unfold fitTermErr fitTermBound fitE5 fitE4 fitE3 at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ## The stated property -/

/-- The exact fitness term `w·x - p·(x - t)²`. -/
def fitExact (x w : Nat → Rat) (t p : Rat) (i : Nat) : Rat := w i * x i - p * ((x i - t) * (x i - t))

/-- **Numerical property of `fitness`.** For `n` equal-length elements with finite values
`|xᵢ| ≤ B`, `|wᵢ| ≤ W`, a finite `target` with `|t| ≤ B` and a finite `penalty` with `|p| ≤ P`,
under the overflow preconditions `2B < 2^1023`, `D² < 2^1023` and `n·(T + η)·ρⁿ < 2^1023`
(`D = fitD B`, `T = fitTermBound B W P`, `ρ = 1 + u`): `fitness` returns a finite value `q`
(no NaN, no infinity, no panic) with `|q| ≤ n·(T + η)·ρⁿ`, within
`n·(u·n·(T + η)·ρⁿ + η) + n·E` (`E = fitTermErr B W P`) of the exact
`∑ (wᵢ·xᵢ - p·(xᵢ - t)²)`. -/
theorem fitness_error (xs ws : Array Zig.F64) (target penalty : Zig.F64)
    (hs : xs.size < 2 ^ 64) (hlen : xs.size = ws.size) {x w : Nat → Rat} {t p B W P : Rat}
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hP : 0 ≤ P)
    (hx : ∀ i (h : i < xs.size), xs[i].toRat? = some (x i) ∧ -B ≤ x i ∧ x i ≤ B)
    (hw : ∀ i (h : i < ws.size), ws[i].toRat? = some (w i) ∧ -W ≤ w i ∧ w i ≤ W)
    (ht : target.toRat? = some t ∧ -B ≤ t ∧ t ≤ B)
    (hp : penalty.toRat? = some p ∧ -P ≤ p ∧ p ≤ P)
    (hov2B : 2 * B < Ω64) (hovD : fitD B * fitD B < Ω64)
    (hov : xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size < Ω64) :
    ∃ r q, fitness xs ws target penalty = pure r ∧ r.toRat? = some q ∧
      -(xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size) ≤ q ∧
      q ≤ xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size ∧
      q - Zig.ratSum (fitExact x w t p) xs.size ≤
        xs.size * (u64 * xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size + η64) +
          xs.size * fitTermErr B W P ∧
      Zig.ratSum (fitExact x w t p) xs.size - q ≤
        xs.size * (u64 * xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size + η64) +
          xs.size * fitTermErr B W P := by
  have hu := Rat.le_of_lt (Zig.FloatFmt.unitRoundoff_pos .f64)
  have hη := Rat.le_of_lt (Zig.FloatFmt.underflowError_pos .f64)
  have hρ : (1 : Rat) ≤ 1 + u64 := by grind
  -- `T ≥ 0`: every summand of `fitTermBound` is.
  have hT : 0 ≤ fitTermBound B W P := by
    have hD : 0 ≤ fitD B := by
      have := Rat.mul_nonneg hu (show 0 ≤ 2 * B by grind); unfold fitD fitE1; grind
    have hQ : 0 ≤ fitQ B := by
      have h1 := Rat.mul_nonneg hD hD
      have := Rat.mul_nonneg hu h1; unfold fitQ fitE2; grind
    have hR : 0 ≤ fitR B P := by
      have h1 := Rat.mul_nonneg hP hQ
      have := Rat.mul_nonneg hu h1; unfold fitR fitE3; grind
    have hX : 0 ≤ fitX B W := by
      have h1 := Rat.mul_nonneg hW hB
      have := Rat.mul_nonneg hu h1; unfold fitX fitE4; grind
    have := Rat.mul_nonneg hu (show 0 ≤ fitX B W + fitR B P by grind)
    unfold fitTermBound fitE5; grind
  -- Every term is finite: `T ≤ n·(T + η)·ρⁿ < 2^1023` once there is a term.
  have hterm : ∀ k < xs.size, ∃ v, (fitTerm xs ws target penalty k).toRat? = some v ∧
      v - fitExact x w t p k ≤ fitTermErr B W P ∧ fitExact x w t p k - v ≤ fitTermErr B W P ∧
      -fitTermBound B W P ≤ v ∧ v ≤ fitTermBound B W P := by
    intro k hk
    have hmono := Zig.uniformBound_mono (Nat.zero_lt_of_lt hk) hρ hη hT
    have hovT : fitTermBound B W P < Ω64 := by grind
    exact fitTerm_error xs ws target penalty hk (hlen ▸ hk) hB hW hP (hx k hk)
      (hw k (hlen ▸ hk)) ht hp hov2B hovD hovT
  let v : Nat → Rat := fun k => ((fitTerm xs ws target penalty k).toRat?).getD 0
  have hv : ∀ k < xs.size, (fitTerm xs ws target penalty k).toRat? = some (v k) ∧
      v k - fitExact x w t p k ≤ fitTermErr B W P ∧ fitExact x w t p k - v k ≤ fitTermErr B W P ∧
      -fitTermBound B W P ≤ v k ∧ v k ≤ fitTermBound B W P := by
    intro k hk
    obtain ⟨y, hy, h⟩ := hterm k hk
    simp only [v, hy, Option.getD_some]
    exact ⟨trivial, h⟩
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := Zig.sumLeft_error_uniform (fmt := .f64)
    (init := Zig.Float.ofBits (0 : BitVec 64)) (t := fitTerm xs ws target penalty) (v := v)
    dot_init_toRat hT (fun k hk => ⟨(hv k hk).1, (hv k hk).2.2.2⟩) hov
  obtain ⟨d1, d2⟩ := Zig.ratSum_sub_le (n := xs.size) (v := v) (w := fitExact x w t p)
    (fun k hk => ⟨(hv k hk).2.1, (hv k hk).2.2.1⟩)
  exact ⟨_, r, fitness_eq_sumLeft xs ws target penalty hs hlen, hr, h1, h2, by grind, by grind⟩

/-- **NaN condition of `fitness`.** A NaN element of `xs` or `ws` at an index in range, or a
NaN `target` or `penalty` with at least one element, makes the result NaN. -/
theorem fitness_isNaN (xs ws : Array Zig.F64) (target penalty : Zig.F64)
    (hs : xs.size < 2 ^ 64) (hlen : xs.size = ws.size) {i : Nat} (hi : i < xs.size)
    (h : xs[i].isNaN = true ∨ (ws[i]'(hlen ▸ hi)).isNaN = true ∨ target.isNaN = true ∨
      penalty.isNaN = true) :
    ∃ r, fitness xs ws target penalty = pure r ∧ r.isNaN = true := by
  refine ⟨_, fitness_eq_sumLeft xs ws target penalty hs hlen, Zig.sumLeft_isNaN _ _ hi ?_⟩
  simp only [fitTerm, getElem!_pos xs i hi, getElem!_pos ws i (hlen ▸ hi)]
  -- A NaN in `d = x - target` reaches the penalty product; a NaN `w`/`x` reaches `w * x`.
  have hpen : ∀ {d : Zig.F64}, d.isNaN = true →
      (Zig.Float.mul penalty (Zig.Float.mul d d)).isNaN = true :=
    fun hd => Zig.mul_isNaN_right _ (Zig.mul_isNaN_left hd _)
  rcases h with h | h | h | h
  · exact Zig.sub_isNaN_left (Zig.mul_isNaN_right _ h) _
  · exact Zig.sub_isNaN_left (Zig.mul_isNaN_left h _) _
  · exact Zig.sub_isNaN_right _ (hpen (Zig.sub_isNaN_right _ h))
  · exact Zig.sub_isNaN_right _ (Zig.mul_isNaN_left h _)

/-- **Stable threshold comparison.** Under `fitness_error`'s hypotheses, when the exact fitness
exceeds a finite threshold `z` (value `ζ`) by more than the error bound, the computed fitness
compares greater than `z`. -/
theorem fitness_gt_of_gap (xs ws : Array Zig.F64) (target penalty z : Zig.F64)
    (hs : xs.size < 2 ^ 64) (hlen : xs.size = ws.size) {x w : Nat → Rat} {t p B W P ζ : Rat}
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hP : 0 ≤ P)
    (hx : ∀ i (h : i < xs.size), xs[i].toRat? = some (x i) ∧ -B ≤ x i ∧ x i ≤ B)
    (hw : ∀ i (h : i < ws.size), ws[i].toRat? = some (w i) ∧ -W ≤ w i ∧ w i ≤ W)
    (ht : target.toRat? = some t ∧ -B ≤ t ∧ t ≤ B)
    (hp : penalty.toRat? = some p ∧ -P ≤ p ∧ p ≤ P)
    (hov2B : 2 * B < Ω64) (hovD : fitD B * fitD B < Ω64)
    (hov : xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size < Ω64)
    (hz : z.toRat? = some ζ)
    (hgap : ζ + (xs.size * (u64 * xs.size * (fitTermBound B W P + η64) * (1 + u64) ^ xs.size +
      η64) + xs.size * fitTermErr B W P) < Zig.ratSum (fitExact x w t p) xs.size) :
    ∃ r, fitness xs ws target penalty = pure r ∧ Zig.Float.lt z r = true := by
  obtain ⟨r, q, hfit, hq, -, -, -, herr⟩ :=
    fitness_error xs ws target penalty hs hlen hB hW hP hx hw ht hp hov2B hovD hov
  exact ⟨r, hfit, Zig.lt_of_error hq hz herr hgap⟩
