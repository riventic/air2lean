import ZigLean.Float.Ops

/-!
# `compiler-rt` semantics (opt-in)

`f128` has no hardware divide, and x86-64 baseline has no FMA instruction, so on that target
`@divExact`/`/` on `f128` and `@mulAdd` on any format lower to compiler_rt calls whose result
differs from the model's own (IEEE-correct) `Float.div`/`Float.fma` (`docs/floats.md`
§Semantics, groups A/B). This file ports those compiler_rt functions bit-exactly. Reachable
only through `--float-semantics compiler-rt` (`Air2Lean/Main.lean`); the default (`ieee`) mode
never calls into it.

Every helper below is `private`: nothing outside this file names them, only the four
`Float.divRt`/`Float.divTruncRt`/`Float.divFloorRt`/`Float.fmaRt` entry points (and the Zig 0.16.0
`Float.divRt016` family) do.
-/

namespace Zig

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
the function. Every step here is `Float.add`/`Float.sub`/`Float.mul` — hardware round-to-nearest
arithmetic, which is exactly what Dekker's technique needs and exactly what the model already
computes correctly for every format (`docs/floats.md`). -/

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
underflow or overflow in the intermediate products). -/
private def ddMul {fmt : FloatFmt} (split a b : Float fmt) : DD fmt :=
  let p1 := Float.mul a split
  let ha := Float.add (Float.sub a p1) p1
  let la := Float.sub a ha
  let p2 := Float.mul b split
  let hb := Float.add (Float.sub b p2) p2
  let lb := Float.sub b hb
  let p3 := Float.mul ha hb
  let q := Float.add (Float.mul ha lb) (Float.mul la hb)
  let hi := Float.add p3 q
  let lo := Float.add (Float.add (Float.sub p3 hi) q) (Float.mul la lb)
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
    Float.add (Float.mul x y) z
  else if !z.isFinite then
    z
  else if x.isZero || y.isZero then
    Float.add (Float.mul x y) z
  else if z.isZero then
    Float.mul x y
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
  let rounded := (quotient + roundUp) % (2 * implicit)
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

end Zig
