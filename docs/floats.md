# Floats

The model of `f16`, `f32`, `f64`, `f80` and `f128` (`ZigLean/Float/`) and the target it follows.

## Reference target

Zig leaves some float results to the target. The model follows **Zig 0.16.0, 0.15.2 and 0.14.1, LLVM backend, `-OReleaseSafe`, x86_64-linux, `-mcpu=baseline`**, the CI target; §Per-version differences lists what differs between the versions. `scripts/floatprobe.sh` (CI step "Float target probe") runs `tests/floatprobe/probe.zig` there and compares its output with `tests/floatprobe/expected.txt`, where `tests/floatprobe/expected.<version>.txt` replaces the lines that differ for that version. A difference means that the target or the Zig version changed a case the model depends on. On a host that is not x86_64-linux, `scripts/diff.sh` counts a mismatch of a function in `tests/diff/<ex>/host.txt` (the float results that differ by target: NaN bits, f80, the sign of a zero) as `host`, not as a failure.

The float diff test counts only on this target. On other targets (e.g. arm64 macOS: native f16, other `@min` zero rule, soft f80) exclude the float examples with `AIR2LEAN_EXAMPLES`.

## Semantics

Every rounding op computes the exact result as a `Rat` and rounds it once to the format (round to nearest, ties to even; overflow → ±inf; subnormals). Exceptions are listed per op.

| Zig | AIR | Model |
|---|---|---|
| `+ - * /` | `add sub mul div_float` | rounded exact result; IEEE 754 rules for inf, NaN and signed zero. `/` on `f128`: §`--float-semantics` group A |
| `@mulAdd` | `mul_add` (args `[lhs, rhs, addend]`) | rounded once. f16: rounded to f32, then to f16. f80: rounded to f128, then to f80. `compiler-rt` mode: §`--float-semantics` group B. f80 invalid encoding: §`--float-semantics` group C |
| `@divTrunc`, `@divFloor` | `div_trunc`, `div_floor` | `trunc(a / b)`, `floor(a / b)`: the division rounds first. `f128`: §`--float-semantics` group A |
| `@divExact` | with safety: `div_trunc`, `floor`, `cmp_eq`, panic `exactDivisionRemainder`; without: `div_exact` | the ops themselves; `div_exact` = `/`. `f128`: §`--float-semantics` group A |
| `@rem` | `rem` | `a − b·trunc(a / b)`, exact (`frem`); the sign of a zero result is the sign of `a`. f80 invalid encoding: §`--float-semantics` group C |
| `@mod` | `mod` | `a < 0 ? rem(rem(a, b) + b, b) : rem(a, b)` (the LLVM lowering). f80 invalid encoding: §`--float-semantics` group C |
| `@sqrt` | `sqrt` | correctly rounded. Before 0.16.0, f128: §Per-version differences |
| `@floor @ceil @trunc` | `floor ceil trunc_float` | exact. f80 invalid encoding: §`--float-semantics` group C |
| `@round` | `round` | nearest integer, ties away from zero. f80 invalid encoding: §`--float-semantics` group C |
| `@abs`, `-x` | `abs`, `neg` | clear or flip the sign bit (also of a NaN) |
| `@min`, `@max` | `min`, `max` | one NaN operand: the other operand. Two NaNs: NaN. +0 and −0: see below |
| `< <= == != >= >` | `cmp_*` | IEEE: NaN is unordered, `−0 == +0` |
| `@floatCast` | `fptrunc`, `fpext` | rounded / exact; value/class-changing casts: group C; f80→f16 in `compiler-rt` mode: group E |
| `@floatFromInt` | `float_from_int` | rounded (also `u128`/`i128`) |
| `@intFromFloat` | `int_from_float_safe` (0.15.2) | truncate. `x <= floor(min − 1)` or `x >= ceil(max + 1)`: panic `integerPartOutOfBounds` (`.overflow`). NaN: `.unspecified` (the check does not catch it) |
| `@intFromFloat` | `int_from_float` (0.14.1, or no safety) | truncate; out of range or NaN: `.unspecified` |
| `@bitCast` | `bitcast` | the bits; float → int of a NaN: `.unspecified` |
| `@sin @cos @tan @exp @exp2 @log @log2 @log10` | same names | opaque (§Transcendental functions) |

### `--float-semantics ieee | compiler-rt`

The reference target has no hardware `f128` divide and no FMA instruction, so `/`/`@divExact`/`@divTrunc`/`@divFloor` on `f128` and `@mulAdd` on any format actually run a compiler_rt software routine there, not the IEEE-correct result the rest of this page describes. Three rounding/value divergences, opt-in together per translated example:

- **Group A — `f128` division** (`__divtf3`; this paragraph: before Zig 0.16.0; 0.16.0: §Per-version differences): flushes a subnormal quotient to a signed zero instead of rounding it into the subnormal range. Its own source comment states the exact halfway case cannot occur, so every other case — normal range, overflow to infinity, exact zero — is already bit-identical to round-to-nearest-even.
- **Group B — `@mulAdd` on every format**: x86-64 baseline has no FMA instruction, so every format calls compiler_rt. f32 `fmaf` and f16 `__fmah` (`fmaf` on the f32 extensions): the exact product in f64, plus `z` rounded to f64, then rounded to f32 — two roundings, so the result can be one ulp from a single rounding (e.g. f32 `fma(0x3f800001, 0x3f7fffff, 0x28000001)` = `0x3f800000`, not `0x3f800001`). f64 `fma`, f128 `fmaq`, f80 `__fmax` (`fmaq` then rounded to f80): Dekker's algorithm, which gives NaN or an ulp off for some subnormal inputs.
- **Group E — f80→f16 `@floatCast`**: `__truncxfhf2` clears the explicit integer bit before its subnormal conversion and uses a wrapping-u64 sticky-bit expression. For example, f80 `2^-15` converts to f16 `+0`, while correctly-rounded conversion gives `0x0200`. `Float.convRt` ports that helper; IEEE mode keeps correctly-rounded conversion. The relevant helper algorithm is the same in 0.14.1, 0.15.2 and 0.16.0.

`ieee` (default; what a proof assumes) always returns the model's own result for groups A, B and E. `compiler-rt` matches them bit-for-bit (`ZigLean/Float/CompilerRt.lean`) — needed only by code that must match the reference target exactly, e.g. a differential test. Opt in per example via `examples/<ex>/translate.args` (`docs/generated-code.md`); a proof never needs to know the divergence exists unless its example opts in.

Two more divergences hold in **both modes, always** — the two sides disagree on *which* value is correct, not just on rounding, so the model throws `.unspecified` instead of picking one:

- **Group C — result-class changes and f80 invalid encodings** (§f80 below): compiler_rt's software `@floor`/`@ceil`/`@trunc`/`@round`/`@rem`/`@mod`/`@mulAdd` read an unnormal/pseudo-infinity/pseudo-NaN operand's raw bits directly and diverge from x87 hardware on them. `@mulAdd` also checks a second f80 sub-case: a pseudo-denormal operand. `fma`'s f128-extension step re-derives the value from the exponent by the ordinary subnormal formula, ignoring the explicit integer bit, and reads it as `0` instead of the modeled value — `Float.isPseudoDenormalF80` (`ZigLean/Float/Ops.lean`), checked by `fmaChk`/`fmaRtChk` and the cast wrappers below. `@floor`/`@ceil`/`@trunc`/`@round`/`@rem`/`@mod` read a pseudo-denormal correctly and need no such guard.
- **Group D — f32/f64 `@min`/`@max` of `+0` and `−0`** (see the table below): order- and sign-dependent on real SSE hardware.

Group C also covers three direct `@floatCast` cases through `Float.convChk` and
`Float.convRtChk`, in both modes. f80→f128 rejects invalid encodings and pseudo-denormals:
`__extendxftf2` can read them as a different value or class (the zero-fraction
pseudo-denormal becomes zero). f80→f16 rejects invalid encodings: `__truncxfhf2` can
read an unnormal as a finite value or a pseudo-infinity as infinity. Pseudo-denormals
underflow to the same signed zero in both f16 conversion modes and need no guard.
f128→f80 rejects NaNs whose entire payload is in the low
49 fraction bits: `__trunctfxf2` discards those bits without setting a quiet bit and
returns infinity. Other NaN conversions retain the usual unspecified sign/payload rule.

### +0 and −0 in `@min` / `@max`

| Format | `@min(+0, −0)`, `@min(−0, +0)` | `@max(+0, −0)`, `@max(−0, +0)` |
|---|---|---|
| f32, f64 | `.unspecified` (group D) | `.unspecified` (group D) |
| f16, f80, f128 | −0 | +0 |

f32/f64 use SSE `minss`/`maxss` sequences: real hardware gives an order- and sign-dependent result for both `@min` and `@max`, confirmed against the reference target. f16/f80/f128 use compiler_rt `fmin`/`fmax`, which order the zeros explicitly and so stay deterministic in both modes.

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

The first two rows are group C for `@floor`/`@ceil`/`@trunc`/`@round`/`@rem`/`@mod`/`@mulAdd` and direct casts to f16 or f128 (`.unspecified`, both modes, always; §`--float-semantics` above). The third row (pseudo-denormal) is group C for `@mulAdd` and for a direct cast to f128;
the model otherwise decodes its value as shown above.

## Per-version differences

The model is one set of defs. Where a Zig version gives a different result, the emitter picks the def for the version that wrote the AIR (`FCtx.zigVersion` in `Air2Lean/Emit.lean`), so the generated code states that version's rule. The translations differ only on these lines (`tests/golden/<version>/<ex>/Gen.lean`).

| Op | 0.14.1, 0.15.2 | 0.16.0 | Source |
|---|---|---|---|
| f128 `@sqrt` | `fpext(sqrt(fptrunc x to f64))`: `Zig.Float.sqrtF128ViaF64` | correctly rounded: `Zig.Float.sqrt` | compiler_rt `sqrtq` (`sqrt.zig`, a musl port since 0.16.0) |
| f128 `/`, `@divExact`, `@divTrunc`, `@divFloor`, `compiler-rt` mode | subnormal quotient flushed to ±0 (group A): `Zig.Float.divRt` … | subnormal quotient rounded from a 113-bit quotient that can be one unit low, and a deep underflow wraps its shift amount (the unchecked `@intCast` to `u7`): `Zig.Float.divRt016` …, a bit-exact port, equal to 0.16.0 on 80,000 random quotients and 3,145,632 edge cases (every divisor exponent) | compiler_rt `__divtf3` (`divtf3.zig`) |

The probe checks the `sqrt` rows on the reference target (`tests/floatprobe/expected.0.16.0.txt`); the diff test (`floatops`, `compiler-rt` mode) checks the division rows.

## Transcendental functions

Zig gives no accuracy for `@sin` etc. The model declares each one as an `opaque` function per format: a proof cannot compute it or assume a property of it.

The differential test runs the real functions: `tests/diff/libm/` builds a static library that calls the compiler_rt functions (`sin`, `sinf`, `__sinh`, `__sinx`, `sinq`, …) by their Zig names, and the Lean side calls it through `@[extern]`. A plain `@sin` in that library would be a call to the symbol `sin`, which the linker of the Lean executable can bind to the system libm. On x86_64-linux the harness links no libc, so its `@sin` is compiler_rt's too. compiler_rt computes f80 and f128 transcendental functions in f64.
