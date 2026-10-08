# aarch64 ABI qualification (T04)

Two aarch64 profiles are qualified separately: **aarch64-linux-gnu** (`-mcpu=baseline` =
`generic`) and **aarch64-macos-none** (`-mcpu=baseline` = `apple_m1`). Both use stock Zig
0.16.0, the LLVM backend and ReleaseSafe. Each profile has three pieces of evidence:

1. A native probe run. `scripts/aarch64-abi.py` runs only on the profile's own host. It does
   not use an emulator or cross execution.
2. A versioned expected file. The probe output must equal it line for line.
3. A Lean check tied to that file. Kernel-checked layout tables are compared with the file, and
   the recorded results are compared with the model.

This is ABI qualification only. aarch64-linux AIR stays outside the translator's accepted
profiles (`Air2Lean/Air/Profile.lean`). No native differential test or proof build runs on
that host. See [target-matrix.md](target-matrix.md).

```sh
# On the profile's host (aarch64 Linux or Apple silicon macOS), with stock Zig 0.16.0:
python3 scripts/aarch64-abi.py check --zig /path/to/zig --target aarch64-linux-gnu
python3 scripts/aarch64-abi.py check --zig /path/to/zig --target aarch64-macos-none
# Any host:
python3 scripts/aarch64-abi.py compare --target aarch64-linux-gnu OBSERVED.txt
lake build ZigLean.VecMem ZigLean.Float.Allowed
lake env lean --run tests/roadmap/aarch64-abi/Model.lean aarch64-linux-gnu \
  tests/roadmap/aarch64-abi/expected/0.16.0/aarch64-linux-gnu-ReleaseSafe.txt
python3 -m unittest discover -s tests/roadmap/aarch64-abi -p 'test_*.py'
```

## Probes

`observe` and `check` build and run three things:

- `tests/roadmap/aarch64-abi/probe.zig` prints:
  - metadata and the features that affect floats and atomics (`lse`, `lse2`,
    `outline_atomics`, `rcpc`, `fullfp16`, …);
  - layout and memory image of `u7`, `i7`, `u24`, `i24`, `u40`, `i40`, `u65`, `u96`, `u128`
    and `i128`, plus wrapping/division/shift results;
  - layout and the image of `1.0` for `f16`…`f128` and `c_longdouble`;
  - f80 and f128 results: `1/3`, `sqrt(2)`, NaN sign and payload (`0/0`, `nan+1`, `-nan`),
    subnormal rounding (`tiny*0.5`, `tiny*1.5`, `min_normal*0.5`, `min_normal-tiny`),
    overflow, `@mulAdd`, conversions to and from f64, u128 and u64;
  - the f80 invalid encodings: unnormal, pseudo-infinity, pseudo-NaN and pseudo-denormal;
  - atomic cells `u8`…`u128`, including `u24` and `u40`, each with padding `00` and `ff`:
    size, alignment, raw cell bytes, then cmpxchg, fetch-add, xchg and load results;
  - `std.atomic.cache_line`.
- L09's `tests/roadmap/vector-layouts/probe.zig`: bit-packed vector sizes, alignments and
  memory images.
- `tests/roadmap/aarch64-abi/atomic-limit.zig`: a `u256` `@atomicRmw`. The compiler must
  reject it with "expected 128-bit integer type or smaller". This records the widest
  atomic integer.

## Expected results and compare

`tests/roadmap/aarch64-abi/expected/<zig>/<triple>-<mode>.txt` holds the native output for
that Zig version. The file's `meta` lines name the target, CPU, mode and Zig version, so
another profile's output does not match. `compare` checks the observation byte for byte:

| Status | Exit | Meaning |
| --- | --- | --- |
| `match` | 0 | equal to the expected file |
| `mismatch` | 1 | any differing, missing or extra line (a diff is printed) |
| `excluded` | 3 | wrong host, or no expected file for this Zig version |

An exclusion is never a match. It exits non-zero, CI fails on it, and no record counts it
as evidence. A copied observation file is not an execution attestation. Only `check` on the
native host, as run by the `aarch64-linux` and `macos` CI jobs, observes the target.

## Profile-tied proofs

`tests/roadmap/aarch64-abi/Model.lean` holds the two profiles' layout tables as Lean data
(`T04.linuxGnu`, `T04.macosNone`). It also holds two theorems, checked by the kernel:
`linuxGnu_layouts` and `macosNone_layouts`. Each states `Recorded.consistent`: every
recorded row equals the model's layout. That covers integer and float `Enc.size`/`Enc.align`,
including the profile's `c_longdouble` format; vector `packedVecLayout`/`boolVecLayout`; and
atomic cells, which must be naturally aligned (size = alignment) and at most the recorded
128-bit limit.

At run time, the file's layout lines must equal the table of the profile named on the
command line, so the theorem is about that file. Each float result line must be allowed by
the default (`ieee`) float model (`Float.Allowed`: bit for bit, or any NaN when the model
gives NaN). Each atomic line must be the sequential result of the model's `cmpxchgAt`/
`atomicRmwAt`. CI also passes the file's vector lines to L09's
`tests/roadmap/vector-layouts/Model.lean`, which compares the byte images with
`Vec.packedEnc`.

### Declared divergences

These results differ from the model on **both** profiles. `Model.lean` lists them. It
prints each one as a divergence and never counts it as a match. It fails if a listed case
starts to match (the list is stale) or if an unlisted case diverges.

| Case | aarch64 (both) | Model / x86_64 reference |
| --- | --- | --- |
| `isnan(f80 unnormal)` | `false`: compiler_rt soft f80 treats it as a number | `true` (x87 and `Float.classify`) |
| `f80 pseudo-denormal + 0` | encoding kept (`0000_8000…`) | normalized (`0001_8000…`) |
| `u24` cmpxchg, padding byte `ff` | **fails**, although the 24-bit values are equal | succeeds |
| `u40` cmpxchg, padding bytes `ff` | **fails**, although the 40-bit values are equal | succeeds |

The model allows `unnormal + 0` itself, because it classifies the returned unnormal as a NaN.
The divergence shows up in `isnan`.

The cmpxchg rows are a synchronization boundary. Zig widens a `u24`/`u40` atomic to its
4-/8-byte ABI cell and compares the whole cell, padding included. A plain store writes only
the value bytes. The model leaves padding undefined and compares only the value bits. So
the model's strong cmpxchg claim is not valid for widths with whole padding bytes (`u24`,
`u40`, `u48`, `u56`, `u65`…`u120`). The translator's atomic checker (`atomicIntChild`)
does not reject them yet (see the risks in the T04 handoff). Widths without padding (`u8`,
`u16`, `u32`, `u64`, `u128`) match on both profiles, with either padding.

## Per-profile observations (Zig 0.16.0, ReleaseSafe)

The two expected files differ only in these lines:

| Observation | aarch64-linux-gnu | aarch64-macos-none |
| --- | --- | --- |
| CPU | `generic` | `apple_m1` |
| `lse`, `lse2`, `rcpc`, `fullfp16` | 0 (LL/SC loops; `outline_atomics` 0) | 1 |
| `c_longdouble` | f128: size 16, align 16, 128 bits | f64: size 8, align 8, 64 bits |

Both profiles share the rest:

- Integers use the x86_64 rules (`intSize`/`intAlign`). `u24` is 4/4, `u40` is 8/8, and
  `u65`, `u96`, `u128` and `i128` are 16/16.
- `f80` is 16/16 with 80 value bits, and `f128` is 16/16.
- Vector images are identical to L09's recorded aarch64-macos file.
- The NaN of an invalid operation is positive (`7fff8…`/`7fffc…`). The model allows it; the
  x86_64 reference gives a negative NaN for f16…f80.
- Subnormal rounding and conversions are as the model predicts.
- Atomics are accepted up to 128 bits and the cache line is 128 bytes.

## Scope

Not covered:

- other modes (ReleaseFast: [build-modes.md](build-modes.md));
- `compiler-rt` float mode, libm and the float operations not listed above;
- vector float arithmetic;
- multi-threaded atomic behaviour (one thread runs the probe);
- ordering strength (LDAR/STLR vs LL/SC);
- other Zig versions. A new version needs its own `expected/<version>/` files; without
  them `compare` reports `excluded`.
