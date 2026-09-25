# Floats

The model of `f16`, `f32`, `f64`, `f80` and `f128` (`ZigLean/Float/`) and the target it follows.

## Reference target

Zig leaves some float results to the target. The model follows **Zig 0.15.2, LLVM backend, `-OReleaseSafe`, x86_64-linux, `-mcpu=baseline`**, the CI target. `scripts/floatprobe.sh` (CI step "Float target probe") runs `tests/floatprobe/probe.zig` there and compares its output with `tests/floatprobe/expected.txt`. A difference means that the target or the Zig version changed a case the model depends on.

The float diff test counts only on this target. On other targets (e.g. arm64 macOS: native f16, other `@min` zero rule, soft f80) exclude the float examples with `AIR2LEAN_EXAMPLES`.

## Semantics

Every rounding op computes the exact result as a `Rat` and rounds it once to the format (round to nearest, ties to even; overflow → ±inf; subnormals). Exceptions are listed per op.

| Zig | AIR | Model |
|---|---|---|
| `+ - * /` | `add sub mul div_float` | rounded exact result; IEEE 754 rules for inf, NaN and signed zero |
| `@mulAdd` | `mul_add` (args `[lhs, rhs, addend]`) | f32, f64, f128: rounded once. f16: rounded to f32, then to f16 (`__fmah`). f80: rounded to f128, then to f80 (`__fmax`) |
| `@divTrunc`, `@divFloor` | `div_trunc`, `div_floor` | `trunc(a / b)`, `floor(a / b)`: the division rounds first |
| `@divExact` | with safety: `div_trunc`, `floor`, `cmp_eq`, panic `exactDivisionRemainder`; without: `div_exact` | the ops themselves; `div_exact` = `/` |
| `@rem` | `rem` | `a − b·trunc(a / b)`, exact (`frem`); the sign of a zero result is the sign of `a` |
| `@mod` | `mod` | `a < 0 ? rem(rem(a, b) + b, b) : rem(a, b)` (the LLVM lowering) |
| `@sqrt` | `sqrt` | correctly rounded. f128: `fpext(sqrt(fptrunc x to f64))` (compiler_rt `sqrtq`) |
| `@floor @ceil @trunc` | `floor ceil trunc_float` | exact |
| `@round` | `round` | nearest integer, ties away from zero |
| `@abs`, `-x` | `abs`, `neg` | clear or flip the sign bit (also of a NaN) |
| `@min`, `@max` | `min`, `max` | one NaN operand: the other operand. Two NaNs: NaN. +0 and −0: see below |
| `< <= == != >= >` | `cmp_*` | IEEE: NaN is unordered, `−0 == +0` |
| `@floatCast` | `fptrunc`, `fpext` | rounded / exact |
| `@floatFromInt` | `float_from_int` | rounded (also `u128`/`i128`) |
| `@intFromFloat` | `int_from_float_safe` (0.15.2) | truncate. `x <= floor(min − 1)` or `x >= ceil(max + 1)`: panic `integerPartOutOfBounds` (`.overflow`). NaN: `.unspecified` (the check does not catch it) |
| `@intFromFloat` | `int_from_float` (0.14.1, or no safety) | truncate; out of range or NaN: `.unspecified` |
| `@bitCast` | `bitcast` | the bits; float → int of a NaN: `.unspecified` |
| `@sin @cos @tan @exp @exp2 @log @log2 @log10` | same names | opaque (§Transcendental functions) |

### +0 and −0 in `@min` / `@max`

| Format | `@min(+0, −0)`, `@min(−0, +0)` | `@max(+0, −0)`, `@max(−0, +0)` |
|---|---|---|
| f32, f64 | +0 | +0 |
| f16, f80, f128 | −0 | +0 |

f32/f64 use SSE `minss`/`maxss` sequences; f16/f80/f128 use compiler_rt `fmin`/`fmax`, which order the zeros explicitly.

### NaN

An op that makes a NaN gives a negative quiet NaN on x86 for f16…f80 and a positive one for f128 (probe: `0/0`). Zig does not define the sign or the payload. The model returns one canonical quiet NaN, so:

- A proof states a NaN result only as `isNaN r`, never as `r = nan`.
- `@bitCast` of a NaN to an integer throws `.unspecified`.
- The diff test prints every NaN as `"nan"`.

### f80

`f80` has an explicit integer bit. Encodings that IEEE formats do not have:

| Encoding | Exponent | Integer bit | Model |
|---|---|---|---|
| unnormal | 1 … 0x7ffe | 0 | NaN |
| pseudo-infinity, pseudo-NaN | 0x7fff | 0 | NaN |
| pseudo-denormal | 0 | 1 | the value `1.f × 2^(1 − 16383)` |

## Transcendental functions

Zig gives no accuracy for `@sin` etc. The model declares each one as an `opaque` function per format: a proof cannot compute it or assume a property of it.

The differential test runs the real functions: `tests/diff/libm/` builds a static library that calls the compiler_rt functions (`sin`, `sinf`, `__sinh`, `__sinx`, `sinq`, …) by their Zig names, and the Lean side calls it through `@[extern]`. A plain `@sin` in that library would be a call to the symbol `sin`, which the linker of the Lean executable can bind to the system libm. On x86_64-linux the harness links no libc, so its `@sin` is compiler_rt's too. compiler_rt computes f80 and f128 transcendental functions in f64.
