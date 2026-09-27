# Zig 0.14.1 vs 0.15.2

## AIR tags (`Air.Inst.Tag`)

| Only in 0.14.1 | Only in 0.15.2 |
|---|---|
| `shuffle` | `shuffle_one`, `shuffle_two` (split of `shuffle`) |
| | `int_from_float_safe`, `int_from_float_optimized_safe` |
| | `memmove` |
| | `runtime_nav_ptr` |

207 tags in 0.14.1, 212 in 0.15.2. None of the differences is in the air2lean subset (floats, SIMD, memory, pointers).

## Exporter port

- `zig-patch/air-json/json.zig` is shared with every version; its `Compat` section has the 0.14.1
  branch: `std.json.WriteStream` over an unbuffered `std.fs.File.Writer`; `Air.extra` is a slice;
  `arg` has no ZIR parameter index (a running count of `arg`s gives the same value in the
  subset); `Value.fmtValue` takes `{}`, not `{f}`; no `int_from_float_safe` tag.
- Hook (`hook.patch`): after `analyzeFnBodyInner` in `src/Zcu/PerThread.zig`, as in 0.15.2.

## Build

0.14.1 cannot link on macOS 26 (Darwin 25): every libc symbol is undefined when it links the build runner. Build it on Linux, for example in a container:

```sh
docker run --rm -v "$PWD":/w -w /w debian:bookworm-slim zig-patch/build.sh 0.14.1
```

(with a host zig 0.14.1 for Linux on `PATH`). The build can go over the declared 7.8 GB memory bound of the compile step ("memory usage peaked at …"); a second run then succeeds with the build cache.

## Observed differences on the examples

The dumps of `basic`, `recursion`, `options`, `floatops`, `floats` and `errors` equal the shared goldens (`tests/golden/<ex>/air/`) apart from `zig_version`. Their translation equals the committed one, except `floatops` (`tests/golden/0.14.1/floatops/Gen.lean`: the f128 compiler_rt rules before 0.16.0, `docs/floats.md` §Per-version differences); CI checks this.

`variants` differs in 2 files. `radius`: the generic panic member has another instance number (`inactiveUnionField__anon_375`; `panicErrorFor?` drops the suffix). `scale`: 0.14.1 stores a union field's payload first, then sets the tag; 0.15.2 and 0.16.0 set the tag first. The translation (`tests/golden/0.14.1/enums/Gen.lean`) differs only in that order and gives the same value (`docs/generated-code.md` §Enums and unions).

`floatconv` differs in 3 files (`toI32`, `toU64`, `toByte`): 0.14.1 lowers `@intFromFloat` to the unchecked `int_from_float` and checks the range after it, so an out-of-range input is undefined before the check. It is not in the 0.14.1 CI job.
