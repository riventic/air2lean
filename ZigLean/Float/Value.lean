import ZigLean.Basic
import ZigLean.Float.Format

/-!
# Float values

`Float fmt`: a bit pattern of the given format. Decoding (`classify`, `toRat?`) and the
canonical encodings (`nan`, `inf`, `zero`). All arithmetic on the fields happens on `Nat`,
via `BitVec.toNat`/`BitVec.ofNat`: `fmt` is a variable, not a literal, so the field widths
are not known at elaboration time.
-/

namespace Zig

/-- A float of format `fmt`, as its raw bits. -/
structure Float (fmt : FloatFmt) where
  bits : BitVec fmt.width
  deriving DecidableEq

instance : Inhabited (Float fmt) := ⟨⟨0#fmt.width⟩⟩

abbrev F16 := Float .f16
abbrev F32 := Float .f32
abbrev F64 := Float .f64
abbrev F80 := Float .f80
abbrev F128 := Float .f128

/-- The value a float bit pattern denotes. `value = (-1)^neg * m * 2^e`. Zero is `finite`
with `m = 0`, its sign kept in `neg`. -/
inductive FloatClass where
  | nan
  | inf (neg : Bool)
  | finite (neg : Bool) (m : Nat) (e : Int)
  deriving DecidableEq, Repr

/-- Pack a sign, a biased exponent field and the bits below it (the fraction for every
format but `f80`, where it is the explicit integer bit followed by the fraction) into a
float. -/
@[inline] def Float.pack (fmt : FloatFmt) (sign : Bool) (exp rest : Nat) : Float fmt :=
  let restW := fmt.width - 1 - fmt.expBits
  ⟨.ofNat fmt.width (((if sign then 1 else 0) <<< (fmt.width - 1)) ||| (exp <<< restW) ||| rest)⟩

/-- Classify a float bit pattern. `f80` has encodings the IEEE formats do not: unnormals,
pseudo-infinities and pseudo-NaNs (`docs/floats.md` §f80) classify as `nan`; pseudo-denormals
classify as the value they encode. -/
def Float.classify {fmt : FloatFmt} (x : Float fmt) : FloatClass :=
  let v := x.bits.toNat
  let sign := x.bits.msb
  let expMask := 2 ^ fmt.expBits - 1
  match fmt with
  | .f80 =>
    let exp := (v >>> (fmt.fracBits + 1)) % (expMask + 1)
    let intBit := (v >>> fmt.fracBits) % 2
    let frac := v % (2 ^ fmt.fracBits)
    if exp = expMask then
      if intBit = 0 then .nan
      else if frac = 0 then .inf sign else .nan
    else if intBit = 0 then
      if exp = 0 then .finite sign frac (fmt.emin - fmt.fracBits) else .nan
    else
      let m := 2 ^ fmt.fracBits + frac
      if exp = 0 then .finite sign m (fmt.emin - fmt.fracBits)
      else .finite sign m ((exp : Int) - fmt.bias - fmt.fracBits)
  | _ =>
    let exp := (v >>> fmt.fracBits) % (expMask + 1)
    let frac := v % (2 ^ fmt.fracBits)
    if exp = expMask then
      if frac = 0 then .inf sign else .nan
    else if exp = 0 then
      .finite sign frac (fmt.emin - fmt.fracBits)
    else
      .finite sign (2 ^ fmt.fracBits + frac) ((exp : Int) - fmt.bias - fmt.fracBits)

@[inline] def Float.isNaN {fmt : FloatFmt} (x : Float fmt) : Bool :=
  match x.classify with
  | .nan => true
  | _ => false

@[inline] def Float.isInf {fmt : FloatFmt} (x : Float fmt) : Bool :=
  match x.classify with
  | .inf _ => true
  | _ => false

@[inline] def Float.isFinite {fmt : FloatFmt} (x : Float fmt) : Bool :=
  match x.classify with
  | .finite .. => true
  | _ => false

/-- The sign bit, read directly off the bits (defined for NaN too). -/
@[inline] def Float.signBit {fmt : FloatFmt} (x : Float fmt) : Bool := x.bits.msb

/-- The real number `(-1)^neg * m * 2^e` a `finite` class denotes. Shared by `toRat?` and by
every op that needs the exact signed value of a finite operand. -/
def finiteToRat (neg : Bool) (m : Nat) (e : Int) : Rat :=
  let mag : Rat := if e ≥ 0 then (m : Rat) * (2 : Rat) ^ e.toNat
    else (m : Rat) / (2 : Rat) ^ (-e).toNat
  if neg then -mag else mag

/-- The real number a float denotes; `none` for NaN and infinity. -/
def Float.toRat? {fmt : FloatFmt} (x : Float fmt) : Option Rat :=
  match x.classify with
  | .nan => none
  | .inf _ => none
  | .finite neg m e => some (finiteToRat neg m e)

/-- `+0` or `-0`. -/
@[inline] def Float.zero {fmt : FloatFmt} (neg : Bool) : Float fmt := Float.pack fmt neg 0 0

/-- `+inf` or `-inf`. `f80` needs the explicit integer bit set, or the pattern reads back
as a pseudo-infinity, i.e. a NaN. -/
@[inline] def Float.inf {fmt : FloatFmt} (neg : Bool) : Float fmt :=
  -- The `rest` match is `Nat`-valued (not `Float fmt`-valued), so it stays a plain,
  -- non-dependent match: matching on `fmt` itself would force each branch's result to the
  -- pattern's specific format, but `fmt` still denotes the general format here.
  let rest : Nat := match fmt with
    | .f80 => 1 <<< fmt.fracBits
    | _ => 0
  Float.pack fmt neg (2 ^ fmt.expBits - 1) rest

/-- The canonical quiet NaN: positive, quiet bit set (`f80`: integer bit set too). Zig
leaves the sign and payload of a NaN result unspecified, so the model always returns this
one bit pattern; a proof states a NaN result only as `isNaN`, never as `= Float.nan`. -/
@[inline] def Float.nan {fmt : FloatFmt} : Float fmt :=
  let rest : Nat := match fmt with
    | .f80 => (1 <<< fmt.fracBits) ||| (1 <<< (fmt.fracBits - 1))
    | _ => 1 <<< (fmt.fracBits - 1)
  Float.pack fmt false (2 ^ fmt.expBits - 1) rest

/-- Reinterpret bits as a float (`@bitCast` into a float). Total: an invalid `f80` encoding
just classifies as NaN. -/
@[inline] def Float.ofBits {fmt : FloatFmt} (bits : BitVec fmt.width) : Float fmt := ⟨bits⟩

/-- `@bitCast` of a float to an integer: NaN has no defined bit pattern to bit-cast. -/
def Float.toBits? {fmt : FloatFmt} (x : Float fmt) : Result (BitVec fmt.width) :=
  if x.isNaN then throw .unspecified else pure x.bits

end Zig
