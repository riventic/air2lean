# Aggregate representation casts and optional pointers (L07)

Zig ≤0.16 `@bitCast` of arrays, `extern` structs and `extern` unions is a memory
reinterpretation with padding bytes undefined (`Zig.reprCast`). Optional pointers convert with
null = address 0, and unwrapping requires non-null. `docs/aggregate-casts.md` gives the rules
and their scope.

| File | Role |
|---|---|
| `probe.zig` | Native probe: the casts' result bytes and the optional-pointer null rules |
| `aarch64-macos-ReleaseSafe.txt` | Its output with stock Zig 0.16.0 (Debug and ReleaseFast print the same) |
| `aggregate_casts.zig` | Source of the exported functions: the probe's casts on runtime operands |
| `air/<version>` | Compiler exports of `aggregate_casts.zig` (0.16.0, 0.15.2, 0.14.1; x86_64-linux ReleaseSafe) |
| `exports.json`, `exports.lock.json` | The export (`scripts/fixture-exports.py`) and its pins: manifest, sources, compilers and every file |
| `air-handwritten/0.16.0` | The earlier hand-written AIR; it translates but is no evidence of the compiler's lowering |
| `AggregateCasts/Gen.lean` | Retained translation of `air/0.16.0` (the 0.15.2 and 0.14.1 exports translate to the same text apart from the profile header) |
| `AggregateCasts/Proofs.lean` | Round trips without padding, `.unspecified` padding results, failed round trips, optional-pointer rules |
| `Model.lean` | The translated casts against a probe output (padding bytes match any native byte) |
| `Checker.lean` | Accepted for 0.14.1/0.15.2/0.16.0 only; layout, bit-size and optional-pointer rejections |

```sh
lake build ZigLean ZigLean.ReprCast Air2Lean air2lean
bash tests/roadmap/aggregate-casts/check.sh            # add --native with AIR2LEAN_ZIG_NATIVE=<stock zig>
```

## Compiler export versus the hand-written AIR

Twelve of the 14 functions export the same instructions as the hand-written files (`bitcast`,
`ret_safe`; the compiler adds `dbg_stmt`) on all three versions. Two differ, both safety checks
that ReleaseSafe emits and the hand-written AIR left out:

- `optFromAddr` (`@ptrFromInt` to `?*u32`): `addr & 3 == 0`, else the `incorrectAlignment` panic,
  then the `bitcast`. A misaligned address panics; the model now reproduces it
  (`optFromAddr_misaligned`).
- `optUnwrap` (`@ptrCast` of `?*u32` to `*u32`): `bitcast` to `usize`, `addr != 0`, else the
  `castToNull` panic, then the `bitcast`. `optUnwrap_some` and `wrap_unwrap` now need a nonzero
  address; the fixture does not change the model.

The compiled functions use `pub fn` plus a `comptime` reference because array parameters are not
allowed in `export fn`. The fresh exports carry the schema 12 profile (`stage2_llvm` x86_64
musl), so `Gen.lean` records a verified profile where the hand-written one recorded
`unverified`.

```sh
python3 -B scripts/fixture-exports.py verify aggregate-casts   # a fresh export equals air/
python3 -B scripts/fixture-exports.py check aggregate-casts    # no compiler: the lock
```
