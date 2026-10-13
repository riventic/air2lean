# Finding: `f80`/`f128` mismatches on aarch64-macos (harness misreport, closed)

Class: SOUNDNESS (reported), resolved as a differential-harness misreport. Status: closed by the
`check_models` gate of `scripts/diff.sh`. The model is correct; no premise and no upstream report
are needed.

## Report

While landing the arena branch, `AIR2LEAN_ZIG_VERSION=0.17.0 AIR2LEAN_CI=1
AIR2LEAN_EXAMPLES=floatops scripts/check.sh` on an aarch64 Mac reported 266 typed mismatches for
Zig 0.17.0 and 0.16.0 and none for 0.15.2: `op80` `@sqrt` 117, `op128` `@sqrt` 130, `/` 11,
`@divFloor` 8. The native `f80` `@sqrt` had about 53 significant bits, and native `f128` `/`,
`@divFloor` and `@sqrt` flushed subnormal operands or results to zero.

## Root cause

The command did not set `AIR2LEAN_ZIG`, so `scripts/diff.sh` built the native harness with the
`zig` on `PATH`, a stock Zig 0.15.2, while the Lean side was the Zig 0.17.0 (0.16.0) translation.
The "native" results were Zig 0.15.2's compiler-rt; the "model" results were the 0.17.0 model,
which is what Zig 0.17.0 compiles.

Counterexample (`examples/floatops/floatops.zig`, aarch64-macos, ReleaseSafe; bit patterns), a
probe that calls the fixture's functions, built with each stock Zig:

| function, input | Zig 0.15.2 native | Zig 0.16.0 and 0.17.0 native | 0.17.0 model |
|---|---|---|---|
| `op80(9, ·)` `@sqrt` `0x4007a7e990f603341000` | `0x4003929aaafd3a805000` | `0x4003929aaafd3a804e6b` | `0x4003929aaafd3a804e6b` |
| `op128(3, ·, 1.0)` `/` `0x0000ffffffffffffffffffffffffffff` | `0x00000000000000000000000000000000` | `0x0000fffffffffffffffffffffffffffe` | `0x0000fffffffffffffffffffffffffffe` |
| `op128(6, ·, 1.0)` `@divFloor` `0x8000ffffffffffffffffffffffffffff` | `0x80000000000000000000000000000000` | `0xbfff0000000000000000000000000000` | `0xbfff0000000000000000000000000000` |
| `op128(9, ·)` `@sqrt` `0x00000000000000000000000000000001` | `0x00000000000000000000000000000000` | `0x1fc80000000000000000000000000000` | `0x1fc80000000000000000000000000000` |

The Zig 0.15.2 column is that version's compiler-rt: `__sqrtx`/`sqrtq` compute
`sqrt(@floatCast(x))` in `f64` (`lib/compiler_rt/sqrt.zig`, "TODO: more correct
implementation"), and its `__divtf3` flushes a subnormal quotient. The Zig 0.15.2 translation
models both (`Float.sqrtF80ViaF64`, `Float.divRt`, `docs/float-semantics.md`), hence no mismatch
for 0.15.2. Zig 0.16.0 replaced both helpers (bit-exact `__sqrtx`/`sqrtq`, the `divtf3.zig` that
`Float.divRt016` ports, including its `…fffe` quotient for a subnormal dividend), and the 0.16.0
and 0.17.0 translations model that. These are fixed upstream behaviours, so nothing is drafted in
`docs/upstream/`.

With the matching stock Zig, the differential is clean on aarch64-macos:
`AIR2LEAN_ZIG=<stock 0.17.0>` and `<stock 0.16.0>` each give `TOTAL floatops: ok=38063
fail_match=23 unspecified=1539 capped=0 mismatch=0`.

## Fix

The harness no longer compares a model with native code of another Zig version. Before the Lean
side runs, `scripts/diff.sh` runs `scripts/check-tree.py check-models <stock Zig version>
<examples>`: a module with a profile record must name that version, and a committed body must
equal the translation `scripts/check.sh` compares for that version on this host
(`docs/generated-code.md`, check trees). Otherwise the run fails in phase `check_models` with a
diagnostic that names both versions; the report from the original command is now:

    error: Proofs/Floatops/Gen.lean is the translation of Zig 0.17.0, the native harness is built
    with Zig 0.15.2: set AIR2LEAN_ZIG to a Zig 0.17.0

Regression: `tests/roadmap/profiles/test_golden_pipeline.py` (`ModelVersionTests`).
