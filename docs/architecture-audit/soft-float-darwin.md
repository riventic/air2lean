# Soundness finding: soft-float `f80`/`f128` results on aarch64-macos differ from the model

Class: SOUNDNESS. Status: open (found while landing the arena branch; `main` at `c90d825b` has
the same 266 mismatches for Zig 0.17.0 and 0.16.0, so it is not caused by the arena branch).

## Finding

On aarch64-macos, `f80` and `f128` arithmetic is soft-float (compiler-rt). For some inputs the
native result is not the IEEE result that the model computes (`ZigLean/Float`, `ieee` float
semantics):

- `@sqrt` of an `f80` is not correctly rounded: the native result has only about 53 significant
  bits (its low bits are zero), the model's is rounded to the 64-bit significand.
- `f128` subnormals: `/`, `@divFloor` and `@sqrt` of a subnormal `f128` operand give the result of
  a zero operand natively (the subnormal is flushed), the model computes with the subnormal.

The model's statements about such a value therefore hold for a value the compiled program does not
produce on this target. The differential test catches it: `scripts/check.sh` (macOS CI job,
`examples/floatops`) reports 266 typed mismatches for Zig 0.17.0 and 0.16.0, none for 0.15.2:
`op80` `@sqrt` 117, `op128` `@sqrt` 130, `/` 11, `@divFloor` 8.

## Counterexample

`examples/floatops/floatops.zig`, `op80(9, a, _, _) = @sqrt(a)` and `op128(sel, a, b, _)`,
aarch64-macos, ReleaseSafe (input, native result, model result; bit patterns):

| function | input | native | model |
|---|---|---|---|
| `op80` `@sqrt` | `0x4007a7e990f603341000` | `0x4003929aaafd3a805000` | `0x4003929aaafd3a804e6b` |
| `op128` `/` | `0x0000ffffffffffffffffffffffffffff` / `1.0` | `0x00000000000000000000000000000000` | `0x0000fffffffffffffffffffffffffffe` |
| `op128` `@divFloor` | `0x8000ffffffffffffffffffffffffffff` / `1.0` | `0x80000000000000000000000000000000` | `0xbfff0000000000000000000000000000` |
| `op128` `@sqrt` | `0x00000000000000000000000000000001` | `0x00000000000000000000000000000000` | `0x1fc80000000000000000000000000000` |

Reproduce: `AIR2LEAN_ZIG_VERSION=0.17.0 AIR2LEAN_CI=1 AIR2LEAN_EXAMPLES=floatops scripts/check.sh`
on an aarch64 Mac (the `MISMATCH (typed)` lines).

## Fix direction

Fail closed per target, not per input: where the target's `f80`/`f128` arithmetic is not IEEE
(soft-float on aarch64-macos), these operations are `.unspecified` in the model (the target's
float semantics label, `docs/float-semantics.md`), or the model follows compiler-rt's algorithm
for that target; the native results are then pinned as unspecified differential cases. Whether
the flushing and the precision loss are compiler-rt bugs is drafted in `docs/upstream/` before
any upstream report (CLAUDE.md, Trusted base).
