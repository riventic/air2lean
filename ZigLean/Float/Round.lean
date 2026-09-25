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

/-- `⌊log₂(n/d)⌋` for `n d : Nat`, both positive: a `Nat.log2` guess, corrected by one
comparison (`ilog2_spec`) — all in `Nat`/`Int`, so no `zpow` (`Rat^Int`) monotonicity is
ever needed, unlike the `Rat`-based `floorLog2` this replaces. -/
private def ilog2 (n d : Nat) : Int :=
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

/-- Round-half-to-even of the (unreduced) fraction `N / D`, `D > 0`. -/
private def roundQuot (N D : Nat) : Int :=
  let m := N / D
  let r := N % D
  if 2 * r < D then (m : Int)
  else if D < 2 * r then (m : Int) + 1
  else if m % 2 = 0 then (m : Int) else (m : Int) + 1

/-- Encode an already-rounded magnitude `m * 2^e` (`m < 2 ^ fmt.prec`, `e` in range).
`m = 0` is a zero; `m < 2 ^ fmt.fracBits` is subnormal. For `f80`, `m` already carries the
explicit integer bit (it is `2 ^ fmt.fracBits + fraction` in the normal case), so the low
`fmt.width - 1 - fmt.expBits` bits are `m` itself in both cases. -/
private def Float.encodeFinite (fmt : FloatFmt) (neg : Bool) (m : Nat) (e : Int) : Float fmt :=
  if m = 0 then Float.zero neg
  else if m < 2 ^ fmt.fracBits then
    Float.pack fmt neg 0 m
  else
    let fieldExp := (e + fmt.bias + fmt.fracBits).toNat
    let rest : Nat := match fmt with
      | .f80 => m
      | _ => m - 2 ^ fmt.fracBits
    Float.pack fmt neg fieldExp rest

/-- Shared tail of every "I already have a correctly-rounded-to-nearest-even mantissa `m0` at
exponent `e0`" computation (`roundRat`, and `Float.sqrt` in `Ops.lean`, which rounds via exact
integer square root instead of `roundTiesEven`). `m0` may carry out to `2 ^ fmt.prec`
(renormalized here); `e0` may put the result out of range (→ `inf`). -/
def Float.finalizeRounded (fmt : FloatFmt) (neg : Bool) (m0 : Int) (e0 : Int) : Float fmt :=
  let (m, e) : Nat × Int :=
    if m0 = (2 : Int) ^ fmt.prec then (2 ^ (fmt.prec - 1), e0 + 1) else (m0.toNat, e0)
  if e + (fmt.prec - 1 : Int) > fmt.emax then Float.inf neg else Float.encodeFinite fmt neg m e

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

end Zig
