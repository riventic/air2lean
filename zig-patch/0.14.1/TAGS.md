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

- `src/Air/json.zig`: ported from 0.15.2. Writes schema 1 (the 0.15.2 exporter writes schema 2 with error unions; that part is not ported yet).
- Hook: the same place as in 0.15.2, after `analyzeFnBodyInner` in `src/Zcu/PerThread.zig`.

## Build

0.14.1 cannot link on macOS 26 (Darwin 25): every libc symbol is undefined when it links the build runner. Build it on Linux, for example in a container:

```sh
docker run --rm -v "$PWD":/w -w /w debian:bookworm-slim zig-patch/build.sh 0.14.1
```

(with a host zig 0.14.1 for Linux on `PATH`). The build can go over the declared 7.8 GB memory bound of the compile step ("memory usage peaked at …"); a second run then succeeds with the build cache.

## Observed differences on examples/basic

The 8 dumps in `tests/golden/0.14.1/air/` are equal to the 0.15.2 schema-1 dumps, except for `zig_version`.
