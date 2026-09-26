import ZigLean.Float.Value

/-!
# Rounding

`Float.roundRat`: round an exact rational value to a float, to nearest, ties to even.
Every arithmetic op computes its exact result as a `Rat` and rounds it once through this
function (`docs/floats.md` §Semantics).
-/

namespace Zig

/-- One correction step towards `k` with `2^k ≤ q < 2^(k+1)`, `q > 0`. `guess` is off by at
most 1 in either direction, so `fuel = 4` always finishes with room to spare. -/
private def floorLog2Fix (q : Rat) (k : Int) : Nat → Int
  | 0 => k
  | fuel + 1 =>
    if q < (2 : Rat) ^ k then floorLog2Fix q (k - 1) fuel
    else if (2 : Rat) ^ (k + 1) ≤ q then floorLog2Fix q (k + 1) fuel
    else k

/-- `⌊log₂ q⌋` for `q > 0`, exact. -/
private def floorLog2 (q : Rat) : Int :=
  let guess : Int := (Nat.log2 q.num.toNat : Int) - (Nat.log2 q.den : Int)
  floorLog2Fix q guess 4

/-- Round a nonnegative rational to the nearest integer, ties to even. -/
private def roundTiesEven (r : Rat) : Int :=
  let fl := r.floor
  let frac := r - (fl : Rat)
  let half : Rat := 1 / 2
  if frac < half then fl
  else if half < frac then fl + 1
  else if fl % 2 = 0 then fl else fl + 1

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
    let p : Int := fmt.prec
    -- `Max.max`: plain `max` would resolve to `Zig.max` (the `BitVec` one) in this namespace.
    let e0 := Max.max (floorLog2 q - (p - 1)) (fmt.emin - (p - 1))
    let m0 := roundTiesEven (q / (2 : Rat) ^ e0)
    Float.finalizeRounded fmt neg m0 e0

end Zig
