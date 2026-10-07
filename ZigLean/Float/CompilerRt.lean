import ZigLean.Float.Ops

/-!
# `compiler-rt` semantics (opt-in)

`f128` has no hardware arithmetic, and x86-64 baseline has no FMA instruction, so on that target
`*`/`@divExact`/`/` on `f128`, `@mulAdd` on any format and f80→f16 conversion lower to compiler_rt
calls whose result differs from the model's own IEEE-correct operations (`docs/floats.md`
§Semantics, groups A/B/E–H). This file ports those compiler_rt functions. Reachable
only through `--float-semantics compiler-rt` (`Air2Lean/Main.lean`); the default (`ieee`) mode
never calls into it.

The implementation helpers are `private`; the public entry points select a target helper,
apply its shared guards and expose the version-specific variants.
-/

namespace Zig

/-! ## f128 multiplication (`mulf3.zig`, `wideMultiply`)

The source's u128 wide multiplication omits a carry from its low half into its high half.
Keep its limb arithmetic here rather than replacing it with an exact 256-bit product. -/

private def wideMultiply128 (a b : Nat) : Nat × Nat :=
  let mask32 := 2 ^ 32 - 1
  let mask64 := 2 ^ 64 - 1
  let maskHi := mask64 - mask32
  let word (x i : Nat) := (x >>> (32 * i)) &&& mask32
  let sum (k : Nat) := (List.range 4).foldl (fun s i =>
    if i ≤ k && k - i < 4 then s + word a i * word b (k - i) else s) 0
  let s0 := sum 0
  let s1 := sum 1
  let s2 := sum 2
  let s3 := sum 3
  let s4 := sum 4
  let s5 := sum 5
  let s6 := sum 6
  let r0 := (s0 &&& mask64) + ((s1 &&& mask32) <<< 32)
  let r1 := (s0 >>> 64) + ((s1 >>> 32) &&& mask64) +
    (s2 &&& mask64) + ((s3 <<< 32) &&& maskHi)
  let lo := (r0 + (r1 <<< 64)) % 2 ^ 128
  let hi := ((r1 >>> 64) + (s1 >>> 96) + (s2 >>> 64) +
    (s3 >>> 32) + s4 + (s5 <<< 32) + (s6 <<< 64)) % 2 ^ 128
  (hi, lo)

private def mulF128 (a b : Float .f128) : Float .f128 :=
  match a.classify, b.classify with
  | .finite sa ma _, .finite sb mb _ =>
    if ma = 0 || mb = 0 then Float.zero (sa != sb) else Id.run do
      let modulus := 2 ^ 128
      let implicit := 2 ^ 112
      let mask := implicit - 1
      let aExp := (a.bits.toNat >>> 112) % 2 ^ 15
      let bExp := (b.bits.toNat >>> 112) % 2 ^ 15
      let normalize (exp sig : Nat) : Nat × Int :=
        if exp = 0 then
          let shift := 112 - Nat.log2 sig
          (sig <<< shift, 1 - (shift : Int))
        else (sig ||| implicit, 0)
      let (asig, ascale) := normalize aExp (a.bits.toNat % implicit)
      let (bsig, bscale) := normalize bExp (b.bits.toNat % implicit)
      let (hi0, lo0) := wideMultiply128 asig (bsig <<< 15)
      let mut hi := hi0
      let mut lo := lo0
      let mut exp : Int := (aExp : Int) + bExp - 16383 + ascale + bscale
      if hi &&& implicit != 0 then exp := exp + 1
      else
        hi := ((hi <<< 1) ||| (lo >>> 127)) % modulus
        lo := (lo <<< 1) % modulus
      if exp ≥ 0x7fff then return Float.inf (sa != sb)
      let mut result := 0
      if exp ≤ 0 then
        let shift := (1 - exp).toNat
        if shift ≥ 128 then return Float.zero (sa != sb)
        let sticky := if (lo <<< (128 - shift)) % modulus != 0 then 1 else 0
        lo := (((hi <<< (128 - shift)) ||| (lo >>> shift)) % modulus) ||| sticky
        hi := hi >>> shift
        result := hi
      else result := (hi &&& mask) ||| (exp.toNat <<< 112)
      if lo > 2 ^ 127 then result := result + 1
      else if lo = 2 ^ 127 then result := result + result % 2
      return Float.ofBits (.ofNat 128 (result ||| ((if sa != sb then 1 else 0) <<< 127)))
  | _, _ => Float.mul a b

/-- Compiler-rt multiplication: f128 follows `mulf3` and its wide-multiply helper;
the hardware formats keep correctly-rounded multiplication. -/
def Float.mulRt {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  if h : fmt = .f128 then h ▸ mulF128 (h ▸ a) (h ▸ b) else Float.mul a b

/-- `__fmodx` returns the original bits when the signless representations compare smaller.
For canonical inputs its remaining integer remainder algorithm agrees with `Float.rem`. -/
def Float.remRt {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  if fmt = .f80 && a.isFinite && b.isFinite && !Float.eq b (Float.zero false) &&
      a.abs.bits.toNat < b.abs.bits.toNat then a
  else Float.rem a b

def Float.modRt {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  if Float.lt a (Float.zero false) then Float.remRt (Float.add (Float.remRt a b) b) b
  else Float.remRt a b

def Float.remRtChk {fmt : FloatFmt} (a b : Float fmt) : Result (Float fmt) :=
  if a.isInvalidF80 || b.isInvalidF80 then throw .unspecified else pure (Float.remRt a b)

def Float.modRtChk {fmt : FloatFmt} (a b : Float fmt) : Result (Float fmt) :=
  if a.isInvalidF80 || b.isInvalidF80 then throw .unspecified else pure (Float.modRt a b)

/-- Before 0.16.0, f80 floor/ceil extend to f128 first. The extension of a pseudo-denormal
uses its fraction with exponent zero, discarding the explicit integer bit. -/
private def legacyRoundInput {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  if x.isPseudoDenormalF80 then
    Float.roundRat fmt x.signBit (finiteToRat false (x.bits.toNat % 2 ^ 63) (-16445))
  else x

def Float.floorRtLegacyChk {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt) :=
  if x.isInvalidF80 then throw .unspecified else pure (Float.floor (legacyRoundInput x))

def Float.ceilRtLegacyChk {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt) :=
  if x.isInvalidF80 then throw .unspecified else pure (Float.ceil (legacyRoundInput x))

theorem Float.floorRtLegacyChk_eq {fmt : FloatFmt} (x : Float fmt)
    (h : x.isPseudoDenormalF80 = false) : Float.floorRtLegacyChk x = Float.floorChk x := by
  simp [Float.floorRtLegacyChk, Float.floorChk, legacyRoundInput, h]

theorem Float.ceilRtLegacyChk_eq {fmt : FloatFmt} (x : Float fmt)
    (h : x.isPseudoDenormalF80 = false) : Float.ceilRtLegacyChk x = Float.ceilChk x := by
  simp [Float.ceilRtLegacyChk, Float.ceilChk, legacyRoundInput, h]

/-! ## f80 to f16 conversion (`__truncxfhf2`, `truncf.zig`)

The reference target calls the same helper in Zig 0.14.1, 0.15.2 and 0.16.0. It clears
f80's explicit integer bit before denormalization, so ordinary finite inputs can differ
from correctly-rounded conversion. The wrapping-u64 sticky-bit expression below is also
the source expression, not the IEEE discarded-bit test. -/

private def truncF80ToF16 (x : Float .f80) : Float .f16 :=
  match x.classify with
  | .nan => Float.nan
  | .inf s => Float.inf s
  | .finite s _ _ =>
    let exp := (x.bits.toNat >>> 64) % 2 ^ 15
    let frac := x.bits.toNat % 2 ^ 63
    -- Bias difference 16383 - 15 = 16368; the normal exponent range is [1, 30].
    -- Its contribution is a multiple of 2^10, so roundQuot's parity is the source's.
    let absResult :=
      if 16369 ≤ exp && exp < 16399 then
        ((exp - 16368) <<< 10) + (roundQuot frac (2 ^ 53)).toNat
      else if 16399 ≤ exp then 0x7c00
      else
        let shift := 16368 - exp
        if 63 < shift then 0
        else
          let sticky := if (frac <<< shift) % 2 ^ 64 != 0 then 1 else 0
          let denormalized := (frac >>> shift) ||| sticky
          (roundQuot denormalized (2 ^ 53)).toNat
    Float.ofBits (.ofNat 16 (absResult ||| ((if s then 1 else 0) <<< 15)))

/-- `@floatCast` in compiler-rt mode: f80→f16 uses the target's software conversion;
every other valid conversion keeps the mathematical model. The caller applies the
shared value/class guard through `convRtChk`. -/
def Float.convRt (fmt2 : FloatFmt) {fmt : FloatFmt} (x : Float fmt) : Float fmt2 :=
  if h : fmt = .f80 then
    if h2 : fmt2 = .f16 then h2 ▸ truncF80ToF16 (h ▸ x)
    else Float.conv fmt2 x
  else Float.conv fmt2 x

/-- `@floatCast` in compiler-rt mode, with the same guards as `Float.convChk`. -/
def Float.convRtChk (fmt2 : FloatFmt) {fmt : FloatFmt} (x : Float fmt) : Result (Float fmt2) :=
  if x.convNeedsGuard fmt2 then throw .unspecified else pure (Float.convRt fmt2 x)

/-! ## `std.math` infrastructure `fma`/`fmaq` need (`frexp.zig`, `ldexp.zig`/`scalbn.zig`,
`ilogb.zig`). Ported via `classify` and exact `Rat`/`Int` arithmetic, not the source's bit
tricks: each of these has a round-to-nearest-even (or exact, for `frexp`/`ilogb`) contract that
`finiteToRat`/`Float.roundRat` already implements, so re-deriving it here would only risk a
second, divergent implementation of the same rounding rule. -/

/-- Is `x` a `+0` or `-0`. -/
private def Float.isZero {fmt : FloatFmt} (x : Float fmt) : Bool :=
  match x.classify with
  | .finite _ 0 _ => true
  | _ => false

/-- The smallest positive normal value (`math.floatMin`). -/
private def Float.floatMin {fmt : FloatFmt} : Float fmt :=
  -- Same `rest` shape as `Float.inf`/`Float.nan` (`Value.lean`): `f80`'s explicit integer bit.
  let rest : Nat := match fmt with
    | .f80 => 1 <<< fmt.fracBits
    | _ => 0
  Float.pack fmt false 1 rest

/-- `math.copysign`: the magnitude of `x`, the sign of `y`. Defined on every bit pattern
(NaN included), like `Float.abs`/`Float.neg`. -/
private def Float.copysign {fmt : FloatFmt} (x y : Float fmt) : Float fmt :=
  ⟨.ofNat fmt.width (x.abs.bits.toNat ||| ((if y.signBit then 1 else 0) <<< (fmt.width - 1)))⟩

/-- `math.frexp`: `x = significand * 2 ^ exponent`, `|significand| ∈ [0.5, 1)` for finite
nonzero `x`; `frexp(±0) = (±0, 0)`, `frexp(±inf) = (±inf, 0)`, `frexp(nan) = (nan, _)`
(`frexp.zig`). `fma`/`fmaq` only ever call this after checking their argument finite, and (for
`x`, `y`) nonzero, so only the nonzero-finite branch is exercised; the rest is still modelled,
for a total and honest port. `m`'s bit length is `Nat.log2 m + 1` (`classify`'s normal case has
`m ∈ [2 ^ fracBits, 2 ^ (fracBits+1))`, its subnormal case `m < 2 ^ fracBits` — either way `< 2 ^
(Nat.log2 m + 1)`), so shifting it down by `Nat.log2 m + 1` bits lands the significand in `[0.5,
1)` exactly, with no rounding (`m`'s precision fits `fmt` with room to spare, so the division by
a power of two is exact). -/
private def Float.frexp {fmt : FloatFmt} (x : Float fmt) : Float fmt × Int :=
  match x.classify with
  | .nan => (x, 0)
  | .inf s => (Float.inf s, 0)
  | .finite s 0 _ => (Float.zero s, 0)
  | .finite s m e =>
    let k := Nat.log2 m
    (Float.roundRat fmt s ((m : Rat) / (2 : Rat) ^ (k + 1)), (k : Int) + 1 + e)

/-- `math.scalbn`/`math.ldexp`: `x * 2 ^ n`, round to nearest ties to even (`ldexp.zig`'s own
doc comment) — exactly `Float.roundRat`'s contract, so this just shifts the exact value's own
exponent field by `n` before rounding once. NaN and infinity pass through unchanged, matching
`ldexp.zig`'s explicit `isNan`/`!isFinite` early return. -/
private def Float.scalbn {fmt : FloatFmt} (x : Float fmt) (n : Int) : Float fmt :=
  match x.classify with
  | .nan => x
  | .inf s => Float.inf s
  | .finite s m e => Float.roundRat fmt s (finiteToRat s m (e + n))

/-- `math.ilogb`: the binary exponent of `x`, i.e. the `e` in `x = m * 2 ^ e` with `|m| ∈ [1,
2)` (`ilogb.zig`). `fma`/`fmaq` only ever call this on `r.hi` after checking it nonzero and
finite (`if (r.hi == 0.0) return ...` guards every call site), so the `nan`/`inf`/zero sentinels
below are never actually read; they are included anyway, matching `ilogb.zig`'s own constants,
for a total and honest port. -/
private def Float.ilogb {fmt : FloatFmt} (x : Float fmt) : Int :=
  match x.classify with
  | .nan => -(2 ^ 31 : Int)
  | .inf _ => (2 ^ 31 - 1 : Int)
  | .finite _ 0 _ => -(2 ^ 31 : Int)
  | .finite _ m e => (Nat.log2 m : Int) + e

/-! ## Dekker's algorithm (`dd_add`/`dd_mul` in `fma.zig`, `dd_add128`/`dd_mul128` in the same
file). One generic pair: the `f64` and `f128` source versions are the same algorithm, differing
only in the doubling split constant, so `ddMul` takes it as a parameter instead of duplicating
the function. Addition and subtraction use `Float.add`/`Float.sub`; multiplication uses
`Float.mulRt`, so f128 intermediates retain the source's wide-multiply carry behavior.
The f64 operations remain hardware round-to-nearest arithmetic. -/

private structure DD (fmt : FloatFmt) where
  hi : Float fmt
  lo : Float fmt

/-- `dd_add`: exact `a + b`, split into a correctly-rounded `hi` and the rounding error `lo`
(`hi + lo = a + b` exactly, as reals). Assumes `a`, `b` finite. -/
private def ddAdd {fmt : FloatFmt} (a b : Float fmt) : DD fmt :=
  let hi := Float.add a b
  let s := Float.sub hi a
  let lo := Float.add (Float.sub a (Float.sub hi s)) (Float.sub b s)
  ⟨hi, lo⟩

/-- `dd_mul`: exact `a * b`, split the same way. `split` is `2 ^ (prec/2 rounded up) + 1`
(`0x1.0p27 + 1.0` for `f64`, `0x1.0p57 + 1.0` for `f128`); assumes `a`, `b` normalized (no
underflow or overflow in the intermediate products). On f128 the source multiplication
can itself lose a carry, so the target port does not guarantee the split is exact. -/
private def ddMul {fmt : FloatFmt} (split a b : Float fmt) : DD fmt :=
  let p1 := Float.mulRt a split
  let ha := Float.add (Float.sub a p1) p1
  let la := Float.sub a ha
  let p2 := Float.mulRt b split
  let hb := Float.add (Float.sub b p2) p2
  let lb := Float.sub b hb
  let p3 := Float.mulRt ha hb
  let q := Float.add (Float.mulRt ha lb) (Float.mulRt la hb)
  let hi := Float.add p3 q
  let lo := Float.add (Float.add (Float.sub p3 hi) q) (Float.mulRt la lb)
  ⟨hi, lo⟩

/-! ## `add_adjusted`/`add_and_denorm` (`fma.zig`; `128` suffix for the `f128` versions). These
adjust `hi`'s last bit into a sticky bit summarizing `lo`, so that adding `hi` into a
higher-exponent number later (`add_adjusted`) or scaling it down into the subnormal range
(`add_and_denorm`) still rounds correctly overall — genuine double-rounding-avoidance bit
tricks, not a rounding rule with a simpler closed form, so they are ported as the literal
wrapping-unsigned-integer bit operations the source performs, via `Nat` (`Value.lean`'s own
`Float.abs`/`Float.neg` already work this way: raw bits as a `Nat`, truncated by `BitVec.ofNat`
on the way back). -/

/-- `add_adjusted(a, b)`: `a + b` (as `hi`/`lo`), with `hi`'s last bit turned into a sticky bit
when `lo ≠ 0`. -/
private def addAdjusted {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  let sum := ddAdd a b
  let uloi := sum.lo.bits.toNat
  if uloi = 0 then sum.hi
  else
    let uhii := sum.hi.bits.toNat
    if uhii % 2 = 0 then
      let x := (uhii ^^^ uloi) >>> (fmt.width - 2)
      ⟨.ofNat fmt.width (uhii + (2 ^ fmt.width + 1 - x))⟩
    else
      sum.hi

/-- `add_and_denorm(a, b, scale)`: `ldexp(a + b, scale)` with a single rounding error, assuming
the result is subnormal — the same sticky-bit adjustment as `addAdjusted`, but keyed on how many
bits `scalbn scale` will shift out rather than on `hi`'s last bit directly. -/
private def addAndDenorm {fmt : FloatFmt} (a b : Float fmt) (scale : Int) : Float fmt :=
  let sum := ddAdd a b
  let uloi := sum.lo.bits.toNat
  let hi :=
    if uloi = 0 then sum.hi
    else
      let uhii := sum.hi.bits.toNat
      let expField : Nat := (uhii >>> fmt.fracBits) % 2 ^ fmt.expBits
      let bitsLost : Int := -(expField : Int) - scale + 1
      if (bitsLost != 1) == (uhii % 2 == 1) then
        let x := ((uhii ^^^ uloi) >>> (fmt.width - 2)) &&& 2
        ⟨.ofNat fmt.width (uhii + (2 ^ fmt.width + 1 - x))⟩
      else
        sum.hi
  Float.scalbn hi scale

/-! ## FMA (`fma`/`fmaq` in `fma.zig`) -/

/-- `fma`/`fmaq`: `x * y + z` with one rounding error, via Dekker's technique. One generic core
for `f64` and `f128` — like `ddMul`, the two source functions are the same algorithm apart from
the split constant — called at each concrete format by `Float.fmaRt` below; `f80` goes through
this at `f128` and rounds down once more (`__fmax`, same as `Float.fma`'s own `f80` case). -/
private def fmaCore {fmt : FloatFmt} (split : Float fmt) (x y z : Float fmt) : Float fmt :=
  if !x.isFinite || !y.isFinite then
    Float.add (Float.mulRt x y) z
  else if !z.isFinite then
    z
  else if x.isZero || y.isZero then
    Float.add (Float.mulRt x y) z
  else if z.isZero then
    Float.mulRt x y
  else
    let (xs, ex) := Float.frexp x
    let (ys, ey) := Float.frexp y
    let (zs0, ez) := Float.frexp z
    let spread0 := ex + ey - ez
    let zs :=
      if spread0 ≤ 2 * (fmt.prec : Int) then Float.scalbn zs0 (-spread0)
      else Float.copysign Float.floatMin zs0
    let xy := ddMul split xs ys
    let r := ddAdd xy.hi zs
    let spread := ex + ey
    if r.hi.isZero then
      Float.add (Float.add xy.hi zs) (Float.scalbn xy.lo spread)
    else
      let adj := addAdjusted r.lo xy.lo
      if spread + Float.ilogb r.hi > fmt.emin - 1 then
        Float.scalbn (Float.add r.hi adj) spread
      else
        addAndDenorm r.hi adj spread

/-- `fma.zig:32-43` (`fmaf`): the product in `f64` (exact: 24 + 24 bits), plus `z` rounded once
to `f64`, then rounded to `f32`. Both branches of the source return the same value (its TODO:
no double-rounding fix), so the result can differ from one rounding by an ulp. -/
private def fmaf (x y z : Float .f32) : Float .f32 :=
  Float.conv .f32 (Float.add (Float.mul (Float.conv .f64 x) (Float.conv .f64 y)) (Float.conv .f64 z))

/-- `@mulAdd` in `compiler-rt` mode. x86-64 baseline has no FMA instruction, so every format
calls compiler_rt: `f32` `fmaf`, `f16` `__fmah` (`fmaf` on the `f32` extensions, then rounded
to `f16`), `f64` `fma`, `f128` `fmaq`, `f80` `__fmax` (`fmaq` on the `f128` extensions, then
rounded to `f80`). -/
def Float.fmaRt {fmt : FloatFmt} (a b c : Float fmt) : Float fmt :=
  if h : fmt = .f32 then
    h ▸ fmaf (h ▸ a) (h ▸ b) (h ▸ c)
  else if h : fmt = .f16 then
    h ▸ Float.conv .f16 (fmaf (Float.conv .f32 a) (Float.conv .f32 b) (Float.conv .f32 c))
  else if h : fmt = .f64 then
    h ▸ fmaCore (Float.roundRat .f64 false ((2 : Rat) ^ 27 + 1))
        (Float.conv .f64 a) (Float.conv .f64 b) (Float.conv .f64 c)
  else if h : fmt = .f128 then
    h ▸ fmaCore (Float.roundRat .f128 false ((2 : Rat) ^ 57 + 1))
        (Float.conv .f128 a) (Float.conv .f128 b) (Float.conv .f128 c)
  else if h : fmt = .f80 then
    h ▸ Float.conv .f80
        (fmaCore (Float.roundRat .f128 false ((2 : Rat) ^ 57 + 1))
          (Float.conv .f128 a) (Float.conv .f128 b) (Float.conv .f128 c))
  else
    Float.fma a b c

/-! ## `f128` division (`divtf3.zig`) -/

/-- `divtf3.zig:229-240`: a quotient whose correctly-rounded magnitude is a nonzero subnormal is
flushed to a signed zero instead of rounded into the subnormal range; a quotient that rounds up
exactly to the smallest normal is returned unchanged (the source's `writtenExponent == 0` branch
keeps that one case). Every other outcome — normal, infinity, NaN, already-zero — equals
`Float.div`'s own result already: the source's own comment above its rounding step ("the exact
halfway case cannot occur") means its round-up-or-down decision and `roundRat`'s ties-to-even
never actually disagree. -/
private def flushSubnormalResult {fmt : FloatFmt} (r : Float fmt) : Float fmt :=
  match r.classify with
  | .finite s m _ => if m ≠ 0 ∧ m < 2 ^ fmt.fracBits then Float.zero s else r
  | _ => r

/-- `@divExact`/`/` in `compiler-rt` mode. `f128` has no hardware divide, so Zig calls
compiler_rt's soft `__divtf3`; every other format keeps its native hardware divide, matching
`Float.div` exactly. -/
def Float.divRt {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  if fmt = .f128 then flushSubnormalResult (Float.div a b) else Float.div a b

/-- `@divTrunc` in `compiler-rt` mode: division, rounded once (`Float.divRt`), then truncated
toward zero. -/
def Float.divTruncRt {fmt : FloatFmt} (a b : Float fmt) : Float fmt := Float.trunc (Float.divRt a b)

/-- `@divFloor` in `compiler-rt` mode: division, rounded once (`Float.divRt`), then floored. -/
def Float.divFloorRt {fmt : FloatFmt} (a b : Float fmt) : Float fmt := Float.floor (Float.divRt a b)

/-! ## `f128` division, Zig 0.16.0 (`divtf3.zig`)

0.16.0's `__divtf3` no longer flushes a subnormal quotient. It rounds the 113-bit quotient `q`
and shifts it into the subnormal range (`divtf3.zig:213-247`). `q` comes from a truncated
Newton-Raphson reciprocal, so it can be one unit below the exact quotient (the source's residual
then equals `b`); the rounding decision there depends on those bits, not only on the exact value.
So this port computes `q` and the residual exactly as the source does, in `Nat` arithmetic
modulo `2^64`/`2^128` for the source's `u64`/`u128`. The normal-range path is correctly rounded
(the source's own comment: the halfway case cannot occur), so it stays `Float.div`. -/

/-- `normalize` (`compiler_rt.zig`): shift a nonzero subnormal significand up to the implicit
bit; returns the shifted significand and `1 - shift`. -/
private def normalize128 (sig : Nat) : Nat × Int :=
  let shift := 112 - Nat.log2 sig
  (sig <<< shift, 1 - (shift : Int))

/-- `divtf3.zig`'s result for finite, nonzero `a` and `b` whose quotient is below the normal
range (`writtenExponent < 1`); `none` for every other case (`Float.div` is exact there). -/
private def divtf3Subnormal (a b : Float .f128) : Option (Float .f128) := Id.run do
  let m64 : Nat := 2 ^ 64
  let m128 : Nat := 2 ^ 128
  let implicit : Nat := 2 ^ 112
  let mask : Nat := implicit - 1
  let A := a.bits.toNat
  let B := b.bits.toNat
  let aExp := (A >>> 112) % 2 ^ 15
  let bExp := (B >>> 112) % 2 ^ 15
  let sign := (A ^^^ B) &&& 2 ^ 127
  let mut aSig := A % implicit
  let mut bSig := B % implicit
  -- NaN, infinity or zero: not this path.
  if aExp == 0x7fff || bExp == 0x7fff then return none
  if (aExp == 0 && aSig == 0) || (bExp == 0 && bSig == 0) then return none
  let mut scale : Int := 0
  if aExp == 0 then
    let (s, k) := normalize128 aSig
    aSig := s; scale := scale + k
  if bExp == 0 then
    let (s, k) := normalize128 bSig
    bSig := s; scale := scale - k
  aSig := aSig ||| implicit
  bSig := bSig ||| implicit
  let mut qExp : Int := (aExp : Int) - bExp + scale
  let q63b := (bSig >>> 49) % m64
  let mut recip64 := (0x7504f333F9DE6484 + m64 - q63b) % m64
  for _ in [0:5] do
    let corr := (m64 - ((recip64 * q63b) >>> 64) % m64) % m64
    recip64 := ((recip64 * corr) >>> 63) % m64
  recip64 := (recip64 + m64 - 1) % m64
  let q127blo := (bSig <<< 15) % m64
  let r64q63 := recip64 * q63b
  let r64q127 := recip64 * q127blo
  let correction := (m128 - (r64q63 + (r64q127 >>> 64)) % m128) % m128
  let r64cH := recip64 * (correction >>> 64)
  let r64cL := recip64 * (correction % m64)
  let reciprocal := ((r64cH + (r64cL >>> 64)) + m128 - 2) % m128
  let mut quotient := (((aSig <<< 2) % m128) * reciprocal) >>> 128
  let mut residual := 0
  if quotient < 2 * implicit then
    residual := ((aSig <<< 113) % m128 + m128 - (quotient * bSig) % m128) % m128
    qExp := qExp - 1
  else
    quotient := quotient >>> 1
    residual := ((aSig <<< 112) % m128 + m128 - (quotient * bSig) % m128) % m128
  let written := qExp + 16383
  if written ≥ 1 then return none
  let roundUp : Nat := if (residual <<< 1) % m128 > bSig then 1 else 0
  if written == 0 then
    -- The source clears the implicit bit and rounds; both of its returns are this value.
    return some (Float.ofBits (BitVec.ofNat 128 (((quotient % implicit) + roundUp) ||| sign)))
  -- `@as(u7, @intCast(1 - writtenExponent))`: compiler_rt is built ReleaseFast, so the cast is
  -- not checked and keeps the low 7 bits. A deep underflow then shifts by less than it should.
  let shift := (1 - written).toNat % 128
  if shift > 112 then return some (Float.ofBits (BitVec.ofNat 128 sign))
  -- `quotient +% @as(u113, …)`: the add is in `u128`, so a carry to `2^113` is kept.
  let rounded := (quotient + roundUp) % m128
  return some (Float.ofBits (BitVec.ofNat 128 (((rounded >>> shift) &&& mask) ||| sign)))

/-- `@divExact`/`/` in `compiler-rt` mode on Zig 0.16.0 (`divtf3.zig` above for `f128`). -/
def Float.divRt016 {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  if h : fmt = .f128 then
    h ▸ (divtf3Subnormal (h ▸ a) (h ▸ b)).getD (Float.div (h ▸ a) (h ▸ b))
  else Float.div a b

/-- `@divTrunc` in `compiler-rt` mode on Zig 0.16.0. -/
def Float.divTruncRt016 {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  Float.trunc (Float.divRt016 a b)

/-- `@divFloor` in `compiler-rt` mode on Zig 0.16.0. -/
def Float.divFloorRt016 {fmt : FloatFmt} (a b : Float fmt) : Float fmt :=
  Float.floor (Float.divRt016 a b)

/-- `@mulAdd` in `compiler-rt` mode, guarded against group C on any operand — the same guard as
`Float.fmaChk` (`Ops.lean`), around `Float.fmaRt` instead of `Float.fma`. -/
def Float.fmaRtChk {fmt : FloatFmt} (a b c : Float fmt) : Result (Float fmt) :=
  if a.isInvalidF80 || b.isInvalidF80 || c.isInvalidF80 ||
      a.isPseudoDenormalF80 || b.isPseudoDenormalF80 || c.isPseudoDenormalF80 then
    throw .unspecified
  else pure (Float.fmaRt a b c)

/-! ## `f128` division per Zig version: what each port computes

The specifications of the two division helpers over their whole domain, against IEEE
`Float.div`:

- `Float.divRt` (Zig 0.14.1 and 0.15.2): `Float.div`, except that a nonzero subnormal quotient
  becomes the signed zero of its sign (`Float.divRt_eq_div_of_not_subnormal`,
  `Float.divRt_of_subnormal`; NaN, infinity, zero and normal quotients are in the first).
- `Float.divRt016` (Zig 0.16.0): `Float.div` when an operand is NaN, infinite or zero
  (`Float.divRt016_eq_div_of_special`), and when the binary exponents `log2 m + e` of the
  operands differ by at least −16381, so that `|a / b| > 2^-16382` by the exponents alone
  (`Float.divRt016_eq_div_of_exp`). Otherwise the quotient can be subnormal and
  `divtf3Subnormal` itself is the specification: its rounding reads the truncated
  Newton-Raphson quotient and a deep underflow wraps its shift amount, so it has no closed
  IEEE form here (`docs/floats.md` §Per-version differences).

Both concern the port: its normal range is `Float.div` by construction (see
`divtf3Subnormal`). -/

/-- The exponent and fraction fields of a finite `f128`, read off `classify`. -/
private theorem f128_fields {x : Float .f128} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) :
    (x.bits.toNat >>> 112) % 2 ^ 15 ≠ 0x7fff ∧
    ((x.bits.toNat >>> 112) % 2 ^ 15 = 0 → m = x.bits.toNat % 2 ^ 112 ∧ e = -16494) ∧
    ((x.bits.toNat >>> 112) % 2 ^ 15 ≠ 0 → m = 2 ^ 112 + x.bits.toNat % 2 ^ 112 ∧
      e = ((x.bits.toNat >>> 112) % 2 ^ 15 : Nat) - 16495) := by
  unfold Float.classify at h
  simp only [FloatFmt.expBits, FloatFmt.fracBits, FloatFmt.emin, FloatFmt.bias,
    show (2:Nat) ^ 15 - 1 + 1 = 2 ^ 15 from rfl] at h
  generalize (x.bits.toNat >>> 112) % 2 ^ 15 = E at h ⊢
  by_cases h1 : E = 2 ^ 15 - 1
  · rw [ite_eq_left h1] at h; by_cases hf : x.bits.toNat % 2 ^ 112 = 0 <;> simp [hf] at h
  · rw [ite_eq_right h1] at h
    refine ⟨fun h' => h1 (by simp [h']), ?_, ?_⟩
    · intro h0; subst h0; simp at h; omega
    · intro h0; rw [ite_eq_right h0] at h; simp at h; omega

/-- A finite f128 that is not a signed zero has a finite, non-zero field pair. -/
private theorem f128_finite_of_fields {x : Float .f128}
    (h1 : (x.bits.toNat >>> 112) % 2 ^ 15 ≠ 0x7fff)
    (h2 : ¬((x.bits.toNat >>> 112) % 2 ^ 15 = 0 ∧ x.bits.toNat % 2 ^ 112 = 0)) :
    ∃ s m e, x.classify = .finite s m e ∧ m ≠ 0 := by
  unfold Float.classify
  simp only [FloatFmt.expBits, FloatFmt.fracBits, FloatFmt.emin, FloatFmt.bias,
    show (2:Nat) ^ 15 - 1 + 1 = 2 ^ 15 from rfl]
  generalize (x.bits.toNat >>> 112) % 2 ^ 15 = E at h1 h2 ⊢
  rw [ite_eq_right (by simpa using h1)]
  by_cases h0 : E = 0
  · rw [ite_eq_left h0]; exact ⟨_, _, _, rfl, fun h => h2 ⟨h0, h⟩⟩
  · rw [ite_eq_right h0]; exact ⟨_, _, _, rfl, by omega⟩

/-- NaN, infinity or zero on either side: `divtf3.zig` returns before its subnormal path. -/
private theorem divtf3Subnormal_of_special {a b : Float .f128}
    (h : (∀ s m e, a.classify = .finite s m e → m = 0) ∨
      (∀ s m e, b.classify = .finite s m e → m = 0)) :
    divtf3Subnormal a b = none := by
  have key : ∀ x : Float .f128, (∀ s m e, x.classify = .finite s m e → m = 0) →
      (x.bits.toNat >>> 112) % 2 ^ 15 = 0x7fff ∨
        ((x.bits.toNat >>> 112) % 2 ^ 15 = 0 ∧ x.bits.toNat % 2 ^ 112 = 0) := by
    intro x hx
    by_cases h1 : (x.bits.toNat >>> 112) % 2 ^ 15 = 0x7fff
    · exact .inl h1
    by_cases h2 : (x.bits.toNat >>> 112) % 2 ^ 15 = 0 ∧ x.bits.toNat % 2 ^ 112 = 0
    · exact .inr h2
    obtain ⟨s, m, e, hc, hm⟩ := f128_finite_of_fields h1 h2
    exact absurd (hx s m e hc) hm
  unfold divtf3Subnormal
  rcases h with h | h <;> rcases key _ h with h | ⟨h, h'⟩
  · simp [h]
  · simp [h, h']
  · simp [h]
  · simp [h, h']

/-- `divtf3.zig`'s quotient exponent before its normalization step, biased: the exponent
field, or `normalize128`'s scale for a subnormal operand. -/
private def effExp (x : Float .f128) : Int :=
  if (x.bits.toNat >>> 112) % 2 ^ 15 = 0 then (normalize128 (x.bits.toNat % 2 ^ 112)).2
  else ((x.bits.toNat >>> 112) % 2 ^ 15 : Nat)

/-- The quotient exponent after normalization is `effExp a - effExp b` or one less, so a
difference of at least `2 - 16383` keeps the written exponent at 1 or above. -/
private theorem divtf3Subnormal_of_exp (a b : Float .f128)
    (ha : (a.bits.toNat >>> 112) % 2 ^ 15 ≠ 0x7fff)
    (hb : (b.bits.toNat >>> 112) % 2 ^ 15 ≠ 0x7fff)
    (he : 2 ≤ effExp a - effExp b + 16383) :
    divtf3Subnormal a b = none := by
  unfold divtf3Subnormal
  show Id.run _ = _
  extract_lets m64 m128 implicit mask A B aExp bExp sign aSig bSig scale residual jp1
  have haE : aExp = (a.bits.toNat >>> 112) % 2 ^ 15 := rfl
  have hbE : bExp = (b.bits.toNat >>> 112) % 2 ^ 15 := rfl
  have haS : aSig = a.bits.toNat % 2 ^ 112 := rfl
  have hbS : bSig = b.bits.toNat % 2 ^ 112 := rfl
  unfold effExp at he
  rw [← haE, ← hbE, ← haS, ← hbS] at he
  clear_value m64 m128 mask sign implicit A B aExp bExp aSig bSig
  split
  next h => simp only [Bool.or_eq_true, beq_iff_eq] at h; omega
  split
  · rfl
  have k1 : ∀ t sc,
      2 ≤ (aExp : Int) - bExp + sc - (if bExp = 0 then (normalize128 bSig).2 else 0) + 16383 →
        jp1 () t sc = none := by
    intro t sc hsc
    simp -zeta only [jp1]
    extract_lets aSig1 jp2 bSig2 scale2
    have k2 : ∀ u sc', 2 ≤ (aExp : Int) - bExp + sc' + 16383 → jp2 () u sc' = none := by
      intro u sc' hsc
      simp -zeta only [jp2]
      extract_lets bSig3 qExp q63b recip64 q127blo jp3 qExpm1
      have hbind : ∀ {α : Type} (x : Id α) (f : α → Id (Option (Float .f128))),
          (∀ v, f v = pure none) → x >>= f = pure none := fun x f h => h x
      apply hbind
      intro v
      extract_lets
      have hj : ∀ q x y, 1 ≤ q + 16383 → jp3 () q x y = pure none := by
        intro q x y hq
        simp -zeta only [jp3]
        extract_lets w
        exact ite_eq_left hq
      split
      · exact hj _ _ _ (by simp only [qExpm1, qExp]; omega)
      · exact hj _ _ _ (by simp only [qExp]; omega)
    by_cases h2 : bExp = 0
    · rw [ite_eq_left h2] at hsc
      rw [ite_eq_left (by simpa using h2)]
      exact k2 _ _ (by simp only [scale2]; omega)
    · rw [ite_eq_right h2] at hsc
      rw [ite_eq_right (by simpa using h2)]
      exact k2 _ _ (by omega)
  show (if (aExp == 0) = true then _ else _) = none
  have hs0 : scale = 0 := rfl
  clear_value scale
  generalize normalize128 bSig = nb at k1 he
  by_cases h1 : aExp = 0
  · rw [ite_eq_left (by simpa using h1)]
    rw [ite_eq_left h1] at he
    generalize normalize128 aSig = na at he ⊢
    obtain ⟨s, k⟩ := na
    refine k1 s (scale + k) ?_
    by_cases h2 : bExp = 0
    · rw [ite_eq_left h2] at he ⊢; simp only at he; omega
    · rw [ite_eq_right h2] at he ⊢; simp only at he; omega
  · rw [ite_eq_right (by simpa using h1)]
    rw [ite_eq_right h1] at he
    refine k1 _ _ ?_
    by_cases h2 : bExp = 0
    · rw [ite_eq_left h2] at he ⊢; omega
    · rw [ite_eq_right h2] at he ⊢; omega

/-- `effExp` is the binary exponent `log2 m + e` plus the bias. -/
private theorem effExp_eq {x : Float .f128} {s : Bool} {m : Nat} {e : Int}
    (h : x.classify = .finite s m e) (hm : m ≠ 0) :
    effExp x = (Nat.log2 m : Int) + e + 16383 := by
  obtain ⟨-, h0, h1⟩ := f128_fields h
  unfold effExp
  by_cases hE : (x.bits.toNat >>> 112) % 2 ^ 15 = 0
  · obtain ⟨rfl, rfl⟩ := h0 hE
    rw [ite_eq_left hE]
    have hlt : Nat.log2 (x.bits.toNat % 2 ^ 112) < 112 :=
      (Nat.log2_lt hm).2 (Nat.mod_lt _ (Nat.two_pow_pos _))
    simp only [normalize128]
    omega
  · obtain ⟨rfl, rfl⟩ := h1 hE
    rw [ite_eq_right hE]
    have hlo : 112 ≤ Nat.log2 (2 ^ 112 + x.bits.toNat % 2 ^ 112) :=
      (Nat.le_log2 (by omega)).2 (by omega)
    have hhi : Nat.log2 (2 ^ 112 + x.bits.toNat % 2 ^ 112) < 113 :=
      (Nat.log2_lt (by omega)).2 (by have := Nat.mod_lt x.bits.toNat (Nat.two_pow_pos 112); omega)
    omega

/-- Zig 0.16.0 `f128` division with a NaN, infinite or zero operand (no finite class with a
nonzero mantissa) is IEEE division. -/
theorem Float.divRt016_eq_div_of_special {a b : Float .f128}
    (h : (∀ s m e, a.classify = .finite s m e → m = 0) ∨
      (∀ s m e, b.classify = .finite s m e → m = 0)) :
    Float.divRt016 a b = Float.div a b := by
  show (divtf3Subnormal a b).getD _ = _
  rw [divtf3Subnormal_of_special h]; rfl

/-- Zig 0.16.0 `f128` division of finite nonzero operands whose binary exponents differ by at
least −16381 is IEEE division. -/
theorem Float.divRt016_eq_div_of_exp {a b : Float .f128} {sa sb : Bool} {ma mb : Nat}
    {ea eb : Int} (ha : a.classify = .finite sa ma ea) (hb : b.classify = .finite sb mb eb)
    (hma : ma ≠ 0) (hmb : mb ≠ 0)
    (h : -16381 ≤ ((Nat.log2 ma : Int) + ea) - ((Nat.log2 mb : Int) + eb)) :
    Float.divRt016 a b = Float.div a b := by
  show (divtf3Subnormal a b).getD _ = _
  rw [divtf3Subnormal_of_exp a b (f128_fields ha).1 (f128_fields hb).1
    (by rw [effExp_eq ha hma, effExp_eq hb hmb]; omega)]
  rfl

/-- Zig 0.14.1/0.15.2 `f128` division is IEEE division unless the IEEE quotient is a nonzero
subnormal. -/
theorem Float.divRt_eq_div_of_not_subnormal {a b : Float .f128}
    (h : ∀ s m e, (Float.div a b).classify = .finite s m e → m = 0 ∨ 2 ^ 112 ≤ m) :
    Float.divRt a b = Float.div a b := by
  show flushSubnormalResult (Float.div a b) = Float.div a b
  unfold flushSubnormalResult
  split
  · rename_i s m e hc
    rw [ite_eq_right]
    rcases h s m e hc with h | h <;> simp [FloatFmt.fracBits] <;> omega
  · rfl

/-- Zig 0.14.1/0.15.2 `f128` division flushes a nonzero subnormal IEEE quotient to the signed
zero of its sign. -/
theorem Float.divRt_of_subnormal {a b : Float .f128} {s : Bool} {m : Nat} {e : Int}
    (h : (Float.div a b).classify = .finite s m e) (hm0 : m ≠ 0) (hm : m < 2 ^ 112) :
    Float.divRt a b = Float.zero s := by
  show flushSubnormalResult (Float.div a b) = _
  unfold flushSubnormalResult
  rw [h]; exact ite_eq_left ⟨hm0, hm⟩


/-- Zig 0.14.1/0.15.2 `f128` division with a NaN, infinite or zero operand is IEEE division:
the IEEE quotient is then a NaN, an infinity or a signed zero, never a nonzero subnormal. -/
theorem Float.divRt_eq_div_of_special {a b : Float .f128}
    (h : (∀ s m e, a.classify = .finite s m e → m = 0) ∨
      (∀ s m e, b.classify = .finite s m e → m = 0)) :
    Float.divRt a b = Float.div a b := by
  apply Float.divRt_eq_div_of_not_subnormal
  intro s m e hc
  left
  have hz : ∀ t : Bool, (Float.zero t : Float .f128).classify = .finite t 0 (-16494) := by
    intro t; cases t <;> decide
  have hn : (Float.nan : Float .f128).classify = .nan := by decide
  have hi : ∀ t : Bool, (Float.inf t : Float .f128).classify = .inf t := by
    intro t; cases t <;> decide
  have hr : ∀ (t : Bool) (q : Rat), q = 0 → Float.roundRat .f128 t q = Float.zero t := by
    intro t q hq; subst hq; unfold Float.roundRat; simp
  unfold Float.div at hc
  split at hc <;> (try simp only [hn, hi, hz] at hc)
  case h_1 | h_2 | h_3 | h_4 => cases hc
  case h_5 => cases hc; rfl
  case h_6 sa ma ea sb mb eb hca hcb =>
    split at hc
    · split at hc <;> simp only [hn, hi] at hc <;> cases hc
    · rename_i hmb
      rcases h with h | h
      · rw [hr _ _ (by rw [h _ _ _ hca]; unfold finiteToRat; split <;> split <;>
          simp [Rat.div_def]), hz] at hc
        cases hc; rfl
      · exact absurd (h _ _ _ hcb) hmb

end Zig
