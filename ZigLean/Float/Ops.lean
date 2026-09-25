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
of different sign: `f16`/`f80`/`f128` (compiler_rt `fmin`) give `-0`. For `f32`/`f64` the target
result depends on the operand order, so generated code calls `Float.minChk`, which throws
`.unspecified`; the `+0` here is only a total-function default (`docs/floats.md` §+0 and −0). -/
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
of different sign: `+0` for `f16`/`f80`/`f128` (compiler_rt `fmax`). For `f32`/`f64` generated
code calls `Float.maxChk`, which throws `.unspecified` (`docs/floats.md` §+0 and −0). -/
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

/-- Correctly rounded (`sqrtCore`; `f80` too: x87 `fsqrt`), except `f128`: compiler_rt's
`sqrtq` rounds to `f64`, takes the `f64` root and extends back (`docs/floats.md` §Semantics).
Not `f80` via `f128`: `sqrt` rounded twice is exact only if the inner format has at least
`2 * 64 + 2` bits of precision, and `f128` has 113. -/
def Float.sqrt {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  if h : fmt = .f128 then
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

/-! ## `.unspecified` guards (`docs/floats.md` §Semantics groups C and D; both modes, always)

The reference target (`x86_64-linux -mcpu=baseline`)'s compiler_rt routines diverge from x87
hardware on two input shapes the model itself does not distinguish from an ordinary case, so
without a guard the model would silently disagree with actual Zig output on these inputs
regardless of `--float-semantics`. Each guard wraps the model's own (unmodified) op: the
`.unspecified` throw is the only change, never a different computed value. -/

/-- Group D: real SSE `minss`/`maxss` give an order-and-sign-dependent result for `f32`/`f64`
when one operand is `+0` and the other `-0` — confirmed on real hardware for both `@min` and
`@max` (`tests/diff` sel 16/17 mismatches), unlike `Float.min`/`Float.max`'s own deterministic
choice. `f16`/`f80`/`f128` keep that deterministic result (compiler_rt `fmin`/`fmax`, 0
mismatches there). -/
def Float.minChk {fmt : FloatFmt} (a b : Float fmt) : Result (Float fmt) :=
  match a.classify, b.classify with
  | .finite sa 0 _, .finite sb 0 _ =>
    match fmt with
    | .f32 | .f64 => if sa != sb then throw .unspecified else pure (Float.min a b)
    | .f16 | .f80 | .f128 => pure (Float.min a b)
  | _, _ => pure (Float.min a b)

/-- `@max`'s group D guard: the same condition as `minChk`. -/
def Float.maxChk {fmt : FloatFmt} (a b : Float fmt) : Result (Float fmt) :=
  match a.classify, b.classify with
  | .finite sa 0 _, .finite sb 0 _ =>
    match fmt with
    | .f32 | .f64 => if sa != sb then throw .unspecified else pure (Float.max a b)
    | .f16 | .f80 | .f128 => pure (Float.max a b)
  | _, _ => pure (Float.max a b)

/-- Group C: does `x`'s bit pattern encode an f80 "unnormal", pseudo-infinity or pseudo-NaN —
the explicit integer bit clear while the biased exponent is nonzero. `classify`'s doc comment
folds all three into `.nan`, indistinguishable there from a real NaN; compiler_rt's software
floor/ceil/trunc/round/rem/mod/fma read these bits directly and diverge from x87 hardware on
them. Always `false` for every other format, whose `classify` never folds distinct bit patterns
together. -/
def Float.isInvalidF80 {fmt : FloatFmt} (x : Float fmt) : Bool :=
  match fmt with
  | .f80 =>
    let v := x.bits.toNat
    let exp := (v >>> (fmt.fracBits + 1)) % 2 ^ fmt.expBits
    let intBit := (v >>> fmt.fracBits) % 2
    intBit == 0 && exp != 0
  | _ => false

/-- Group C, `@mulAdd` only: does `x`'s bit pattern encode an f80 pseudo-denormal — the explicit
integer bit set while the biased exponent is zero (`docs/floats.md` §f80: modeled as the value
`1.f × 2^(1 − 16383)`, unlike a true zero/subnormal's clear integer bit). `fma`'s f128-extension
step on the reference target re-derives the value from the exponent alone by the ordinary
subnormal formula, ignoring this explicit bit, and reads it as `0`. `@floor`/`@ceil`/`@trunc`/
`@round`/`@rem`/`@mod` read a pseudo-denormal correctly (0 mismatches there) and need no such
guard. Always `false` for every other format. -/
def Float.isPseudoDenormalF80 {fmt : FloatFmt} (x : Float fmt) : Bool :=
  match fmt with
  | .f80 =>
    let v := x.bits.toNat
    let exp := (v >>> (fmt.fracBits + 1)) % 2 ^ fmt.expBits
    let intBit := (v >>> fmt.fracBits) % 2
    intBit == 1 && exp == 0
  | _ => false

/-- `@floor`, guarded against group C. -/
def Float.floorChk {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt) :=
  if x.isInvalidF80 then throw .unspecified else pure (Float.floor x)

/-- `@ceil`, guarded against group C. -/
def Float.ceilChk {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt) :=
  if x.isInvalidF80 then throw .unspecified else pure (Float.ceil x)

/-- `@trunc` (round-to-integer), guarded against group C. -/
def Float.truncChk {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt) :=
  if x.isInvalidF80 then throw .unspecified else pure (Float.trunc x)

/-- `@round`, guarded against group C. -/
def Float.roundChk {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt) :=
  if x.isInvalidF80 then throw .unspecified else pure (Float.round x)

/-- `@rem`, guarded against group C on either operand. -/
def Float.remChk {fmt : FloatFmt} (a b : Float fmt) : Result (Float fmt) :=
  if a.isInvalidF80 || b.isInvalidF80 then throw .unspecified else pure (Float.rem a b)

/-- `@mod`, guarded against group C on either operand. -/
def Float.modChk {fmt : FloatFmt} (a b : Float fmt) : Result (Float fmt) :=
  if a.isInvalidF80 || b.isInvalidF80 then throw .unspecified else pure (Float.mod a b)

/-- `@mulAdd` in `ieee` mode, guarded against group C on any operand: an invalid encoding or a
pseudo-denormal (`Float.isPseudoDenormalF80`). `compiler-rt` mode's `Float.fmaRtChk`
(`CompilerRt.lean`) applies the identical guard around `Float.fmaRt`. -/
def Float.fmaChk {fmt : FloatFmt} (a b c : Float fmt) : Result (Float fmt) :=
  if a.isInvalidF80 || b.isInvalidF80 || c.isInvalidF80 ||
      a.isPseudoDenormalF80 || b.isPseudoDenormalF80 || c.isPseudoDenormalF80 then
    throw .unspecified
  else pure (Float.fma a b c)

end Zig
