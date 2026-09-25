import ZigLean.Float.Round

/-!
# Float operations

Arithmetic, comparisons and conversions on `Float fmt`, per `docs/floats.md` §Semantics.
Every arithmetic op computes an exact `Rat` (or, for `sqrt`, an exact integer square root)
and rounds it once through `Float.roundRat`/`Float.finalizeRounded` — the format's rounding
schedule (single- vs double-rounded, `docs/floats.md` §f16/f80) picks which format that
round happens at.
-/

namespace Zig

/-- Truncate a rational toward zero. -/
private def truncRat (r : Rat) : Int := if r ≥ 0 then r.floor else r.ceil

/-! ## Sign-bit-only ops -/

/-- Clear the sign bit. Defined for NaN too (only the sign bit moves). -/
def Float.abs {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  ⟨.ofNat fmt.width (x.bits.toNat % 2 ^ (fmt.width - 1))⟩

/-- Flip the sign bit. Defined for NaN too (only the sign bit moves). -/
def Float.neg {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  ⟨.ofNat fmt.width (x.bits.toNat ^^^ (1 <<< (fmt.width - 1)))⟩

/-! ## Comparisons

`toRat?` collapses NaN and infinity to `none` alike, so comparisons go through `classify`
directly: infinities are ordered, only NaN is unordered. -/

/-- `a < b`. NaN is unordered (`false` either side); infinities compare by sign. -/
def Float.lt {fmt : FloatFmt} (a b : Float fmt) : Bool :=
  match a.classify, b.classify with
  | .nan, _ => false
  | _, .nan => false
  | .inf sa, .inf sb => sa && !sb
  | .inf sa, .finite .. => sa
  | .finite .., .inf sb => !sb
  | .finite sa ma ea, .finite sb mb eb => finiteToRat sa ma ea < finiteToRat sb mb eb

/-- `a = b`. NaN is unordered (`false` either side, incl. NaN = NaN); `-0 = +0`. -/
def Float.eq {fmt : FloatFmt} (a b : Float fmt) : Bool :=
  match a.classify, b.classify with
  | .nan, _ => false
  | _, .nan => false
  | .inf sa, .inf sb => sa == sb
  | .inf _, .finite .. => false
  | .finite .., .inf _ => false
  | .finite sa ma ea, .finite sb mb eb => finiteToRat sa ma ea == finiteToRat sb mb eb

def Float.ne {fmt : FloatFmt} (a b : Float fmt) : Bool := !Float.eq a b
def Float.le {fmt : FloatFmt} (a b : Float fmt) : Bool := Float.lt a b || Float.eq a b
def Float.gt {fmt : FloatFmt} (a b : Float fmt) : Bool := Float.lt b a
def Float.ge {fmt : FloatFmt} (a b : Float fmt) : Bool := Float.le b a

/-- `@min`. NaN loses to a non-NaN operand; if both are NaN, the result is NaN. Of two zeros
of different sign: `f32`/`f64` (SSE `minss`) give `+0`; `f16`/`f80`/`f128` (compiler_rt
`fmin`) give `-0` (`docs/floats.md` §+0 and −0 in `@min`/`@max`). -/
def Float.min {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  match a.classify, b.classify with
  | .nan, .nan => Float.nan
  | .nan, _ => b
  | _, .nan => a
  | .finite sa 0 _, .finite sb 0 _ =>
    match fmt with
    | .f32 | .f64 => Float.zero (sa && sb)
    | .f16 | .f80 | .f128 => Float.zero (sa || sb)
  | _, _ => if Float.le a b then a else b

/-- `@max`. NaN loses to a non-NaN operand; if both are NaN, the result is NaN. Of two zeros
of different sign, the result is `+0` (docs: `@max(+0,-0) = @max(-0,+0) = +0`). -/
def Float.max {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  match a.classify, b.classify with
  | .nan, .nan => Float.nan
  | .nan, _ => b
  | _, .nan => a
  | .finite sa 0 _, .finite sb 0 _ => Float.zero (sa && sb)
  | _, _ => if Float.le a b then b else a

/-! ## Conversions -/

/-- `@floatCast`: convert to another format, rounding to nearest, ties to even (`fpext` is
exact because rounding an already-exactly-representable value is a no-op). -/
def Float.conv (fmt2 : FloatFmt) {fmt : FloatFmt} (x : Float fmt) : Float fmt2 :=
  match x.classify with
  | .nan => Float.nan
  | .inf s => Float.inf s
  | .finite s m e => Float.roundRat fmt2 s (finiteToRat s m e)

/-- `@intToFloat`: convert a (signed or unsigned, per `s`) integer to `fmt`, rounding to
nearest, ties to even. `roundRat` takes the sign explicitly, so `v = 0` (giving `+0`) needs
no separate case. -/
def Float.ofInt (fmt : FloatFmt) (s : Bool) {n : Nat} (x : BitVec n) : Float fmt :=
  let v : Int := if s then x.toInt else (x.toNat : Int)
  Float.roundRat fmt (v < 0) (v : Rat)

/-- `@floatToInt`: truncate toward zero into an `n`-bit integer (signed per `s`). `safe`
matches Zig's runtime safety check, i.e. whether the truncated value (incl. NaN, ±inf) is
out of the target type's range: `x ≤ floor(min-1) ∨ x ≥ ceil(max+1)` is, for a
truncate-toward-zero result, exactly "the truncated value is outside `[min, max]`", so this
checks that range directly instead of re-deriving it from the pre-truncation value. Out of
range (or NaN): `.overflow` if `safe`, `.unspecified` otherwise. -/
def Float.toInt {fmt : FloatFmt} (s : Bool) (n : Nat) (safe : Bool) (x : Float fmt) :
    Result (BitVec n) :=
  match x.classify with
  | .nan => throw .unspecified
  | .inf _ => if safe then throw .overflow else throw .unspecified
  | .finite sn m e =>
    let mag : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    let tv : Int := if sn then -(mag : Int) else (mag : Int)
    let lo : Int := if s then -(2 ^ (n - 1) : Int) else 0
    let hi : Int := if s then (2 ^ (n - 1) : Int) - 1 else (2 ^ n : Int) - 1
    if tv < lo || tv > hi then
      if safe then throw .overflow else throw .unspecified
    else pure (.ofInt n tv)

/-! ## Arithmetic

`add`/`mul`/`div` each pass an externally-computed sign into `roundRat`/`finalizeRounded`
rather than relying on the sign of the computed `Rat`, because a `Rat` zero has no sign of
its own (`finiteToRat` of any zero mantissa is the untagged `Rat` `0`) — the sign of a zero
*result* has its own IEEE rule per op, independent of the magnitude computation. -/

def Float.add {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  match a.classify, b.classify with
  | .nan, _ => Float.nan
  | _, .nan => Float.nan
  | .inf sa, .inf sb => if sa == sb then Float.inf sa else Float.nan
  | .inf sa, .finite .. => Float.inf sa
  | .finite .., .inf sb => Float.inf sb
  | .finite sa ma ea, .finite sb mb eb =>
    let sum := finiteToRat sa ma ea + finiteToRat sb mb eb
    -- `x + (-x) = +0`; only `(-0) + (-0) = -0` (docs §Semantics).
    let neg := if sum = 0 then (sa && ma == 0) && (sb && mb == 0) else sum < 0
    Float.roundRat fmt neg sum

/-- `a - b = a + (-b)`, literally: reuses `add`'s special-case handling (incl. its signed-zero
rule) unchanged, since IEEE subtraction is defined the same way. -/
def Float.sub {fmt : FloatFmt} (a b : Float fmt) : Float fmt := Float.add a (Float.neg b)

def Float.mul {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  match a.classify, b.classify with
  | .nan, _ => Float.nan
  | _, .nan => Float.nan
  | .inf sa, .inf sb => Float.inf (sa != sb)
  | .inf sa, .finite sb mb _ => if mb = 0 then Float.nan else Float.inf (sa != sb)
  | .finite sa ma _, .inf sb => if ma = 0 then Float.nan else Float.inf (sa != sb)
  | .finite sa ma ea, .finite sb mb eb =>
    Float.roundRat fmt (sa != sb) (finiteToRat sa ma ea * finiteToRat sb mb eb)

def Float.div {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  match a.classify, b.classify with
  | .nan, _ => Float.nan
  | _, .nan => Float.nan
  | .inf _, .inf _ => Float.nan
  | .inf sa, .finite sb .. => Float.inf (sa != sb)
  | .finite sa .., .inf sb => Float.zero (sa != sb)
  | .finite sa ma ea, .finite sb mb eb =>
    if mb = 0 then
      if ma = 0 then Float.nan else Float.inf (sa != sb)
    else
      Float.roundRat fmt (sa != sb) (finiteToRat sa ma ea / finiteToRat sb mb eb)

/-- The special-value result of `a * b + c`, or `none` if all three are finite (so `fma`
should compute the fused, exactly-once-rounded result). `sp` is the sign the product would
have if it were finite. Splitting the product's special-value handling out this way (instead
of computing `Float.mul a b` and combining with `Float.add`) matters only when the product's
true magnitude would overflow `fmt` while `c` is already infinite: the fused result is still
`c` (a finite value plus an actual infinity is that infinity, regardless of its magnitude),
which a rounded intermediate product could get wrong by overflowing to the wrong-signed
infinity first. -/
private def fmaSpecial {fmt : FloatFmt} (sp : Bool) : FloatClass → Float fmt
  | .nan => Float.nan
  | .inf sc => if sp == sc then Float.inf sp else Float.nan
  | .finite .. => Float.inf sp

/-- `@mulAdd`: `a * b + c`, rounded once — except `f16` (rounds through `f32`) and `f80`
(rounds through `f128`), per `docs/floats.md` §f16/§f80. -/
def Float.fma {fmt : FloatFmt} (a b c : Float fmt) : Float fmt :=
  match a.classify, b.classify, c.classify with
  | .nan, _, _ => Float.nan
  | _, .nan, _ => Float.nan
  | _, _, .nan => Float.nan
  | .inf sa, .finite sb mb _, cc => if mb = 0 then Float.nan else fmaSpecial (sa != sb) cc
  | .finite sa ma _, .inf sb, cc => if ma = 0 then Float.nan else fmaSpecial (sa != sb) cc
  | .inf sa, .inf sb, cc => fmaSpecial (sa != sb) cc
  | .finite .., .finite .., .inf sc => Float.inf sc
  | .finite sa ma ea, .finite sb mb eb, .finite sc mc ec =>
    let signP := sa != sb
    let prodZero := ma == 0 || mb == 0
    let sum := finiteToRat sa ma ea * finiteToRat sb mb eb + finiteToRat sc mc ec
    let neg := if sum = 0 then (signP && prodZero) && (sc && mc == 0) else sum < 0
    if h : fmt = .f16 then
      h ▸ Float.conv .f16 (Float.roundRat .f32 neg sum)
    else if h : fmt = .f80 then
      h ▸ Float.conv .f80 (Float.roundRat .f128 neg sum)
    else
      Float.roundRat fmt neg sum

/-! ## Round-to-integer ops

`@floor`/`@ceil`/`@trunc`/`@round` return a float, not an integer: since a finite `Float fmt`
value has mantissa `m < 2 ^ fmt.prec`, any fractional part (`e < 0`) leaves `|value| <
2 ^ (fmt.prec - 1)`, so its floor/ceil/trunc/round is always itself exactly representable in
`fmt` — `roundRat` never actually rounds here, it only re-encodes an exact integer. A result
of exactly `0` takes the operand's sign (e.g. `@trunc(-0.7) = -0.0`), matching IEEE 754. -/

private def Float.roundToInt {fmt : FloatFmt} (rule : Rat → Int) (x : Float fmt) : Float fmt :=
  match x.classify with
  | .nan => Float.nan
  | .inf s => Float.inf s
  | .finite s m e =>
    let v := rule (finiteToRat s m e)
    if v = 0 then Float.zero s else Float.roundRat fmt (v < 0) (v : Rat)

def Float.floor {fmt : FloatFmt} (x : Float fmt) : Float fmt := Float.roundToInt (·.floor) x
def Float.ceil {fmt : FloatFmt} (x : Float fmt) : Float fmt := Float.roundToInt (·.ceil) x
def Float.trunc {fmt : FloatFmt} (x : Float fmt) : Float fmt := Float.roundToInt truncRat x

/-- `@round`: nearest integer, ties away from zero (unlike arithmetic rounding, which ties to
even). -/
def Float.round {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  Float.roundToInt (fun r =>
    let fl := r.floor
    let frac := r - (fl : Rat)
    let half : Rat := 1 / 2
    if frac < half then fl
    else if half < frac then fl + 1
    else if r ≥ 0 then fl + 1 else fl) x

/-! ## Square root

Correctly rounded via exact integer square root (`Nat.sqrt`), never a `Rat` approximation:
`Real.sqrt` is irrational in general, so no finite `Rat` computation could be *exact*, and an
approximation risks resolving a round-to-nearest-even tie on the wrong side. Shifting the
finite value `m * 2 ^ e` by an even power of two before taking `Nat.sqrt` sidesteps this: the
scaled radicand is an exact integer, so its integer square root's remainder decides the
rounding direction exactly, and a tie (`Real.sqrt shiftedM = root + 1/2`) is provably
impossible (`4 * shiftedM = (2 * root + 1) ^ 2` would need a perfect square that is both a
multiple of 4 and odd). -/

/-- `f80` via `f128` (full precision), `f128` via `f64` (compiler_rt's `sqrtq` truncates to
`f64`, calls `f64`'s `sqrt`, then extends back — `docs/floats.md` §Semantics: `@sqrt` |
`f128: fpext(sqrt(fptrunc x to f64))`, so `f128`'s `@sqrt` is deliberately *not*
correctly-rounded at full precision) — otherwise as `sqrtCore`. -/
def Float.sqrt {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  if h : fmt = .f80 then
    h ▸ Float.conv .f80 (sqrtCore .f128 (Float.conv .f128 x))
  else if h : fmt = .f128 then
    h ▸ Float.conv .f128 (sqrtCore .f64 (Float.conv .f64 x))
  else
    sqrtCore fmt x
where
  /-- `sqrt` for every format directly (no intermediate-format rounding). -/
  sqrtCore (fmt : FloatFmt) (x : Float fmt) : Float fmt :=
    match x.classify with
    | .nan => Float.nan
    | .inf s => if s then Float.nan else Float.inf false
    | .finite s m e =>
      if m = 0 then Float.zero s
      else if s then Float.nan
      else
        let p : Int := fmt.prec
        let ex : Int := (Nat.log2 m : Int) + e
        -- The target exponent for a `p`-bit root, clamped for a subnormal result, and
        -- never past `e.ediv 2` — which keeps `shiftAmt` below non-negative, i.e. the
        -- scaled radicand an exact `Nat` (`e - 2 * (e.ediv 2) = e.emod 2 ≥ 0`, and only
        -- decreasing further from there).
        let te := Min.min (Max.max (ex.ediv 2 - (p - 1)) (fmt.emin - (p - 1))) (e.ediv 2)
        let shiftAmt := (e - 2 * te).toNat
        let shiftedM := m <<< shiftAmt
        let root := Nat.sqrt shiftedM
        let rem := shiftedM - root * root
        let m0 : Int := if rem ≤ root then root else root + 1
        Float.finalizeRounded fmt false m0 te

/-! ## Remainder, modulo, integer division -/

/-- `@rem`: `a - b * trunc(a / b)`, exact — no rounding is needed since the true remainder of
two same-format floats always fits their shared precision. A zero result takes `a`'s sign,
per `docs/floats.md` §Semantics (the arithmetic itself loses it, since a `Rat` zero is
unsigned). -/
def Float.rem {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  match a.classify, b.classify with
  | .nan, _ => Float.nan
  | _, .nan => Float.nan
  | .inf _, _ => Float.nan
  | .finite .., .inf _ => a
  | .finite sa ma ea, .finite sb mb eb =>
    if mb = 0 then Float.nan
    else
      let ra := finiteToRat sa ma ea
      let rb := finiteToRat sb mb eb
      let r := ra - rb * (truncRat (ra / rb) : Rat)
      if r = 0 then Float.zero sa else Float.roundRat fmt (r < 0) r

/-- `@mod`: the LLVM lowering, `a < 0 ? rem(rem(a, b) + b, b) : rem(a, b)`
(`docs/floats.md` §Semantics) — `a < 0` is the ordinary float comparison (`-0` is not `< 0`),
matching `rt` values there against `tests/floatprobe/expected.txt`. -/
def Float.mod {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  if Float.lt a (Float.zero false) then
    Float.rem (Float.add (Float.rem a b) b) b
  else
    Float.rem a b

/-- `@divTrunc`: division, rounded once, then truncated toward zero — not an exact-quotient
truncation. -/
def Float.divTrunc {fmt : FloatFmt} (a b : Float fmt) : Float fmt := Float.trunc (Float.div a b)

/-- `@divFloor`: division, rounded once, then floored. -/
def Float.divFloor {fmt : FloatFmt} (a b : Float fmt) : Float fmt := Float.floor (Float.div a b)

end Zig
