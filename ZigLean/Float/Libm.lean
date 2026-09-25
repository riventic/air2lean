import ZigLean.Float.Value

/-!
# Transcendental functions

`docs/floats.md` §Transcendental functions: Zig specifies no accuracy for `@sin`, `@cos`,
`@tan`, `@exp`, `@exp2`, `@log`, `@log2`, `@log10` — only that the result is *some* float, so
the model treats each one as an uninterpreted (`opaque`) function of its argument: a proof can
state `isNaN`/`isInf`/`isFinite` closure properties about it (if any hold) but never its value.
`Float.libm` carries no defining equation for that reason; `@[implemented_by]` supplies its
runtime behaviour by linking to `tests/diff/libm/libm.zig` (agent E), a static library built
from Zig's own compiler_rt, so `#eval`/the differential tests actually compute real
transcendentals — but neither `ZigLean` itself nor a `lake build` of it needs those symbols to
resolve, only an executable that calls `Float.libm` and gets linked against that library does.

ABI (`tests/diff/libm/libm.zig`'s docstring, verbatim contract): `f16`/`f32`/`f64` pass the
bit pattern as one zero-extended `UInt64`; `f80`/`f128` split it across two `UInt64` halves
(`hi` first in, `hi` first out) since neither fits one register-sized return. Symbol names:
`air2lean_libm_<op>_f<width>` (narrow) / `air2lean_libm_<op>_f<width>_hi`/`_lo` (wide).
-/

namespace Zig

/-- A transcendental op the model exposes; `docs/floats.md` §Transcendental functions. -/
inductive LibmOp where
  | sin | cos | tan | exp | exp2 | log | log2 | log10
  deriving DecidableEq, Repr

/-! ## Extern primitives

One pair of `@[extern]` opaques per op × format, each a direct call into the matching
`tests/diff/libm/libm.zig` export — no logic here beyond naming, so nothing to get wrong
independent of that file's own docstring/contract. -/

@[extern "air2lean_libm_sin_f16"] private opaque sinF16 : UInt64 → UInt64
@[extern "air2lean_libm_sin_f32"] private opaque sinF32 : UInt64 → UInt64
@[extern "air2lean_libm_sin_f64"] private opaque sinF64 : UInt64 → UInt64
@[extern "air2lean_libm_sin_f80_hi"] private opaque sinF80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_sin_f80_lo"] private opaque sinF80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_sin_f128_hi"] private opaque sinF128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_sin_f128_lo"] private opaque sinF128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_cos_f16"] private opaque cosF16 : UInt64 → UInt64
@[extern "air2lean_libm_cos_f32"] private opaque cosF32 : UInt64 → UInt64
@[extern "air2lean_libm_cos_f64"] private opaque cosF64 : UInt64 → UInt64
@[extern "air2lean_libm_cos_f80_hi"] private opaque cosF80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_cos_f80_lo"] private opaque cosF80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_cos_f128_hi"] private opaque cosF128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_cos_f128_lo"] private opaque cosF128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_tan_f16"] private opaque tanF16 : UInt64 → UInt64
@[extern "air2lean_libm_tan_f32"] private opaque tanF32 : UInt64 → UInt64
@[extern "air2lean_libm_tan_f64"] private opaque tanF64 : UInt64 → UInt64
@[extern "air2lean_libm_tan_f80_hi"] private opaque tanF80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_tan_f80_lo"] private opaque tanF80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_tan_f128_hi"] private opaque tanF128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_tan_f128_lo"] private opaque tanF128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_exp_f16"] private opaque expF16 : UInt64 → UInt64
@[extern "air2lean_libm_exp_f32"] private opaque expF32 : UInt64 → UInt64
@[extern "air2lean_libm_exp_f64"] private opaque expF64 : UInt64 → UInt64
@[extern "air2lean_libm_exp_f80_hi"] private opaque expF80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_exp_f80_lo"] private opaque expF80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_exp_f128_hi"] private opaque expF128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_exp_f128_lo"] private opaque expF128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_exp2_f16"] private opaque exp2F16 : UInt64 → UInt64
@[extern "air2lean_libm_exp2_f32"] private opaque exp2F32 : UInt64 → UInt64
@[extern "air2lean_libm_exp2_f64"] private opaque exp2F64 : UInt64 → UInt64
@[extern "air2lean_libm_exp2_f80_hi"] private opaque exp2F80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_exp2_f80_lo"] private opaque exp2F80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_exp2_f128_hi"] private opaque exp2F128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_exp2_f128_lo"] private opaque exp2F128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_log_f16"] private opaque logF16 : UInt64 → UInt64
@[extern "air2lean_libm_log_f32"] private opaque logF32 : UInt64 → UInt64
@[extern "air2lean_libm_log_f64"] private opaque logF64 : UInt64 → UInt64
@[extern "air2lean_libm_log_f80_hi"] private opaque logF80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log_f80_lo"] private opaque logF80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log_f128_hi"] private opaque logF128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log_f128_lo"] private opaque logF128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_log2_f16"] private opaque log2F16 : UInt64 → UInt64
@[extern "air2lean_libm_log2_f32"] private opaque log2F32 : UInt64 → UInt64
@[extern "air2lean_libm_log2_f64"] private opaque log2F64 : UInt64 → UInt64
@[extern "air2lean_libm_log2_f80_hi"] private opaque log2F80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log2_f80_lo"] private opaque log2F80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log2_f128_hi"] private opaque log2F128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log2_f128_lo"] private opaque log2F128Lo : UInt64 → UInt64 → UInt64

@[extern "air2lean_libm_log10_f16"] private opaque log10F16 : UInt64 → UInt64
@[extern "air2lean_libm_log10_f32"] private opaque log10F32 : UInt64 → UInt64
@[extern "air2lean_libm_log10_f64"] private opaque log10F64 : UInt64 → UInt64
@[extern "air2lean_libm_log10_f80_hi"] private opaque log10F80Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log10_f80_lo"] private opaque log10F80Lo : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log10_f128_hi"] private opaque log10F128Hi : UInt64 → UInt64 → UInt64
@[extern "air2lean_libm_log10_f128_lo"] private opaque log10F128Lo : UInt64 → UInt64 → UInt64


/-! ## Dispatch

`Float.libmImpl` picks the (op, format)-specific extern call and marshals `Float fmt`'s bits
to/from the `UInt64`(s) the ABI wants. The `match fmt with` branches all produce a plain `Nat`
(`resultBits`); the `Float fmt`-typed wrapping happens once, outside the match, against the
original unnarrowed `fmt` — matching `Float fmt` inside each branch would only narrow the
*expected type*, not substitute `fmt` in an explicit argument used there (see `Value.lean`'s
`Float.inf`/`Float.nan`). -/

private def Float.libmImpl (op : LibmOp) {fmt : FloatFmt} (x : Float fmt) : Float fmt :=
  let raw := x.bits.toNat
  let resultBits : Nat := match fmt with
    | .f16 =>
      let f : UInt64 → UInt64 := match op with
        | .sin => sinF16 | .cos => cosF16 | .tan => tanF16 | .exp => expF16
        | .exp2 => exp2F16 | .log => logF16 | .log2 => log2F16 | .log10 => log10F16
      (f (UInt64.ofNat raw)).toNat
    | .f32 =>
      let f : UInt64 → UInt64 := match op with
        | .sin => sinF32 | .cos => cosF32 | .tan => tanF32 | .exp => expF32
        | .exp2 => exp2F32 | .log => logF32 | .log2 => log2F32 | .log10 => log10F32
      (f (UInt64.ofNat raw)).toNat
    | .f64 =>
      let f : UInt64 → UInt64 := match op with
        | .sin => sinF64 | .cos => cosF64 | .tan => tanF64 | .exp => expF64
        | .exp2 => exp2F64 | .log => logF64 | .log2 => log2F64 | .log10 => log10F64
      (f (UInt64.ofNat raw)).toNat
    | .f80 =>
      let hi := UInt64.ofNat (raw >>> 64)
      let lo := UInt64.ofNat (raw % 2 ^ 64)
      let fhi : UInt64 → UInt64 → UInt64 := match op with
        | .sin => sinF80Hi | .cos => cosF80Hi | .tan => tanF80Hi | .exp => expF80Hi
        | .exp2 => exp2F80Hi | .log => logF80Hi | .log2 => log2F80Hi | .log10 => log10F80Hi
      let flo : UInt64 → UInt64 → UInt64 := match op with
        | .sin => sinF80Lo | .cos => cosF80Lo | .tan => tanF80Lo | .exp => expF80Lo
        | .exp2 => exp2F80Lo | .log => logF80Lo | .log2 => log2F80Lo | .log10 => log10F80Lo
      ((fhi hi lo).toNat <<< 64) ||| (flo hi lo).toNat
    | .f128 =>
      let hi := UInt64.ofNat (raw >>> 64)
      let lo := UInt64.ofNat (raw % 2 ^ 64)
      let fhi : UInt64 → UInt64 → UInt64 := match op with
        | .sin => sinF128Hi | .cos => cosF128Hi | .tan => tanF128Hi | .exp => expF128Hi
        | .exp2 => exp2F128Hi | .log => logF128Hi | .log2 => log2F128Hi | .log10 => log10F128Hi
      let flo : UInt64 → UInt64 → UInt64 := match op with
        | .sin => sinF128Lo | .cos => cosF128Lo | .tan => tanF128Lo | .exp => expF128Lo
        | .exp2 => exp2F128Lo | .log => logF128Lo | .log2 => log2F128Lo | .log10 => log10F128Lo
      ((fhi hi lo).toNat <<< 64) ||| (flo hi lo).toNat
  ⟨.ofNat fmt.width resultBits⟩

/-- `@sin`/`@cos`/`@tan`/`@exp`/`@exp2`/`@log`/`@log2`/`@log10`: no defining equation (see the
module docstring) — `Float.libmImpl` supplies the compiled behaviour. -/
@[implemented_by Float.libmImpl]
opaque Float.libm (op : LibmOp) {fmt : FloatFmt} (x : Float fmt) : Float fmt

end Zig
