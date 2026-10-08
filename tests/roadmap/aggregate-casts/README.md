# Aggregate representation casts and optional pointers (L07)

Zig ≤0.16 `@bitCast` of arrays, `extern` structs and `extern` unions is a memory
reinterpretation with padding bytes undefined (`Zig.reprCast`). Optional pointers convert with
null = address 0, and unwrapping requires non-null. `docs/aggregate-casts.md` gives the rules
and their scope.

| File | Role |
|---|---|
| `probe.zig` | Native probe: the casts' result bytes and the optional-pointer null rules |
| `aarch64-macos-ReleaseSafe.txt` | Its output with stock Zig 0.16.0 (Debug and ReleaseFast print the same) |
| `air/0.16.0` | Hand-written AIR in the exporter's schema for the probe's casts |
| `AggregateCasts/Gen.lean` | Retained translation of `air/0.16.0` |
| `AggregateCasts/Proofs.lean` | Round trips without padding, `.unspecified` padding results, failed round trips, optional-pointer rules |
| `Model.lean` | The translated casts against a probe output (padding bytes match any native byte) |
| `Checker.lean` | Accepted for 0.14.1/0.15.2/0.16.0 only; layout, bit-size and optional-pointer rejections |

```sh
lake build ZigLean ZigLean.ReprCast Air2Lean air2lean
bash tests/roadmap/aggregate-casts/check.sh            # add --native with AIR2LEAN_ZIG_NATIVE=<stock zig>
```
