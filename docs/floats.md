# Floats

The model of `f16`, `f32`, `f64`, `f80` and `f128` (`ZigLean/Float/`) and the target it follows.

## Reference target

Zig leaves some float results to the target. The model follows **Zig 0.15.2, LLVM backend, `-OReleaseSafe`, x86_64-linux, `-mcpu=baseline`**, the CI target. `scripts/floatprobe.sh` (CI step "Float target probe") runs `tests/floatprobe/probe.zig` there and compares its output with `tests/floatprobe/expected.txt`. A difference means that the target or the Zig version changed a case the model depends on.

The float diff test counts only on this target. On other targets (e.g. arm64 macOS: native f16, other `@min` zero rule, soft f80) exclude the float examples with `AIR2LEAN_EXAMPLES`.

## Semantics

Every rounding op computes the exact result as a `Rat` and rounds it once to the format (round to nearest, ties to even; overflow → ±inf; subnormals). Exceptions are listed per op.

| Zig | AIR | Model |
|---|---|---|
| `+ - * /` | `add sub mul div_float` | rounded exact result; IEEE 754 rules for inf, NaN and signed zero. `/` on `f128`: §`--float-semantics` group A |
| `@mulAdd` | `mul_add` (args `[lhs, rhs, addend]`) | f32, f64, f128: rounded once. f16: rounded to f32, then to f16 (`__fmah`). f80: rounded to f128, then to f80 (`__fmax`). f64/f80/f128: §`--float-semantics` group B. f80 invalid encoding: §`--float-semantics` group C |
| `@divTrunc`, `@divFloor` | `div_trunc`, `div_floor` | `trunc(a / b)`, `floor(a / b)`: the division rounds first. `f128`: §`--float-semantics` group A |
| `@divExact` | with safety: `div_trunc`, `floor`, `cmp_eq`, panic `exactDivisionRemainder`; without: `div_exact` | the ops themselves; `div_exact` = `/`. `f128`: §`--float-semantics` group A |
| `@rem` | `rem` | `a − b·trunc(a / b)`, exact (`frem`); the sign of a zero result is the sign of `a`. f80 invalid encoding: §`--float-semantics` group C |
| `@mod` | `mod` | `a < 0 ? rem(rem(a, b) + b, b) : rem(a, b)` (the LLVM lowering). f80 invalid encoding: §`--float-semantics` group C |
| `@sqrt` | `sqrt` | correctly rounded. f128: `fpext(sqrt(fptrunc x to f64))` (compiler_rt `sqrtq`) |
| `@floor @ceil @trunc` | `floor ceil trunc_float` | exact. f80 invalid encoding: §`--float-semantics` group C |
| `@round` | `round` | nearest integer, ties away from zero. f80 invalid encoding: §`--float-semantics` group C |
| `@abs`, `-x` | `abs`, `neg` | clear or flip the sign bit (also of a NaN) |
| `@min`, `@max` | `min`, `max` | one NaN operand: the other operand. Two NaNs: NaN. +0 and −0: see below |
| `< <= == != >= >` | `cmp_*` | IEEE: NaN is unordered, `−0 == +0` |
| `@floatCast` | `fptrunc`, `fpext` | rounded / exact |
| `@floatFromInt` | `float_from_int` | rounded (also `u128`/`i128`) |
| `@intFromFloat` | `int_from_float_safe` (0.15.2) | truncate. `x <= floor(min − 1)` or `x >= ceil(max + 1)`: panic `integerPartOutOfBounds` (`.overflow`). NaN: `.unspecified` (the check does not catch it) |
| `@intFromFloat` | `int_from_float` (0.14.1, or no safety) | truncate; out of range or NaN: `.unspecified` |
| `@bitCast` | `bitcast` | the bits; float → int of a NaN: `.unspecified` |
| `@sin @cos @tan @exp @exp2 @log @log2 @log10` | same names | opaque (§Transcendental functions) |

### `--float-semantics ieee | compiler-rt`

The reference target has no hardware `f128` divide and no FMA instruction, so `/`/`@divExact`/`@divTrunc`/`@divFloor` on `f128` and `@mulAdd` on any format actually run a compiler_rt software routine there, not the IEEE-correct result the rest of this page describes. Two divergences, opt-in together per translated example:

- **Group A — `f128` division** (`__divtf3`): flushes a subnormal quotient to a signed zero instead of rounding it into the subnormal range. Its own source comment states the exact halfway case cannot occur, so every other case — normal range, overflow to infinity, exact zero — is already bit-identical to round-to-nearest-even.
- **Group B — `@mulAdd` on f64, f80, f128** (`fma`, `fmaq`, `__fmax`): a Dekker's-algorithm software emulation of a fused multiply-add, needed because x86-64 baseline has no FMA instruction. f16 and f32 keep native FMA hardware (0 mismatches against the model in the reference-target diff test) and are not ported.

`ieee` (default; what a proof assumes) always returns the model's own result for groups A and B. `compiler-rt` matches them bit-for-bit (`ZigLean/Float/CompilerRt.lean`) — needed only by code that must match the reference target exactly, e.g. a differential test. Opt in per example via `examples/<ex>/translate.args` (`docs/generated-code.md`); a proof never needs to know the divergence exists unless its example opts in.

Two more divergences hold in **both modes, always** — the two sides disagree on *which* value is correct, not just on rounding, so the model throws `.unspecified` instead of picking one:

- **Group C — f80 invalid encodings** (§f80 below): compiler_rt's software `@floor`/`@ceil`/`@trunc`/`@round`/`@rem`/`@mod`/`@mulAdd` read an unnormal/pseudo-infinity/pseudo-NaN operand's raw bits directly and diverge from x87 hardware on them. `@mulAdd` alone has a second f80 sub-case: a pseudo-denormal operand. `fma`'s f128-extension step re-derives the value from the exponent by the ordinary subnormal formula, ignoring the explicit integer bit, and reads it as `0` instead of the modeled value — `Float.isPseudoDenormalF80` (`ZigLean/Float/Ops.lean`), checked only by `fmaChk`/`fmaRtChk`. `@floor`/`@ceil`/`@trunc`/`@round`/`@rem`/`@mod` read a pseudo-denormal correctly and need no such guard.
- **Group D — f32/f64 `@min`/`@max` of `+0` and `−0`** (see the table below): order- and sign-dependent on real SSE hardware.

### +0 and −0 in `@min` / `@max`

| Format | `@min(+0, −0)`, `@min(−0, +0)` | `@max(+0, −0)`, `@max(−0, +0)` |
|---|---|---|
| f32, f64 | `.unspecified` (group D) | `.unspecified` (group D) |
| f16, f80, f128 | −0 | +0 |

f32/f64 use SSE `minss`/`maxss` sequences: real hardware gives an order- and sign-dependent result for both `@min` and `@max`, confirmed against the reference target (a stale earlier version of this table claimed `@max` always gives `+0`; it does not). f16/f80/f128 use compiler_rt `fmin`/`fmax`, which order the zeros explicitly and so stay deterministic in both modes.

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

The first two rows are group C for `@floor`/`@ceil`/`@trunc`/`@round`/`@rem`/`@mod`/`@mulAdd` (`.unspecified`, both modes, always; §`--float-semantics` above). The third row (pseudo-denormal) is a correctly-modeled value everywhere except `@mulAdd`, where it is group C too.

## Transcendental functions

Zig gives no accuracy for `@sin` etc. The model declares each one as an `opaque` function per format: a proof cannot compute it or assume a property of it.

The differential test runs the real functions: `tests/diff/libm/` builds a static library that calls the compiler_rt functions (`sin`, `sinf`, `__sinh`, `__sinx`, `sinq`, …) by their Zig names, and the Lean side calls it through `@[extern]`. A plain `@sin` in that library would be a call to the symbol `sin`, which the linker of the Lean executable can bind to the system libm. On x86_64-linux the harness links no libc, so its `@sin` is compiler_rt's too. compiler_rt computes f80 and f128 transcendental functions in f64.
