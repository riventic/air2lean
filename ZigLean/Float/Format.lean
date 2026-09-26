/-!
# Float formats

The five IEEE-754-family formats the model supports, and the constants that describe
their bit layout. See `docs/floats.md`.
-/

namespace Zig

/-- A float format. `f80` is the x87 extended format: it has an explicit integer bit,
unlike the other formats, which keep it implicit. -/
inductive FloatFmt where
  | f16
  | f32
  | f64
  | f80
  | f128
  deriving DecidableEq, Repr

namespace FloatFmt

/-- Total bit width. -/
@[inline] def width : FloatFmt → Nat
  | f16 => 16
  | f32 => 32
  | f64 => 64
  | f80 => 80
  | f128 => 128

/-- Exponent field width. -/
@[inline] def expBits : FloatFmt → Nat
  | f16 => 5
  | f32 => 8
  | f64 => 11
  | f80 => 15
  | f128 => 15

/-- Stored fraction bits, after the leading bit. For `f80` this is the 63 bits after the
explicit integer bit, not counting that bit. -/
@[inline] def fracBits : FloatFmt → Nat
  | f16 => 10
  | f32 => 23
  | f64 => 52
  | f80 => 63
  | f128 => 112

/-- Precision in bits, including the leading bit (implicit for every format but `f80`,
where it is stored). -/
@[inline] def prec (fmt : FloatFmt) : Nat := fmt.fracBits + 1

/-- Exponent bias. -/
@[inline] def bias (fmt : FloatFmt) : Nat := 2 ^ (fmt.expBits - 1) - 1

/-- Smallest normal (unbiased) exponent. -/
@[inline] def emin (fmt : FloatFmt) : Int := 1 - (fmt.bias : Int)

/-- Largest normal (unbiased) exponent. -/
@[inline] def emax (fmt : FloatFmt) : Int := (fmt.bias : Int)

end FloatFmt

end Zig
