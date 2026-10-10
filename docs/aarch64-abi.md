# aarch64 ABI qualification (T04)

Two aarch64 profiles are qualified separately: **aarch64-linux-gnu** (`-mcpu=baseline` =
`generic`) and **aarch64-macos-none** (`-mcpu=baseline` = `apple_m1`). Both use stock Zig
(0.17.0, 0.16.0, 0.15.2 and 0.14.1, each with its own expected file), the LLVM backend and
ReleaseSafe. Each profile has three pieces of evidence:

1. A native probe run. `scripts/aarch64-abi.py` runs only on the profile's own host. It does
   not use an emulator or cross execution.
2. A versioned expected file. The probe output must equal it line for line.
3. A Lean check tied to that file. Kernel-checked layout tables are compared with the file, and
   the recorded results are compared with the model.

The translator accepts both profiles (`Target.qualified` in `Air2Lean/Air/Dialect.lean`;
[profiles.md](profiles.md#aarch64-abi-profiles-t04)). aarch64-linux only for the Zig versions
with an expected file (`Target.aarch64Probed`: 0.17.0, 0.16.0, 0.15.2 and 0.14.1, on both
profiles) and, on aarch64-linux, the `gnu` ABI: any other is a profile error.
See [target-matrix.md](target-matrix.md) and §Translation below.

```sh
# On the profile's host (aarch64 Linux or Apple silicon macOS), with a stock Zig whose version
# has an expected file (0.17.0, 0.16.0, 0.15.2, 0.14.1):
python3 scripts/aarch64-abi.py check --zig /path/to/zig --target aarch64-linux-gnu
python3 scripts/aarch64-abi.py check --zig /path/to/zig --target aarch64-macos-none
# Any host:
python3 scripts/aarch64-abi.py compare --target aarch64-linux-gnu OBSERVED.txt
lake build ZigLean.VecMem ZigLean.Float.Allowed ZigLean.Mem.Thread
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
  - `std.atomic.cache_line`;
  - synchronization boundaries (`rmw`, `order`, `atomic_ext`, `litmus` rows): every
    `@atomicRmw` operation (`Xchg`, `Add`, `Sub`, `And`, `Nand`, `Or`, `Xor`, `Max`, `Min`) on
    `u8`/`i8`, `u24`/`i24`, `u40`/`i40`, `u64`/`i64` and `u128`/`i128` cells, with operands that
    separate signed from unsigned `Max`/`Min`; the result of every ordering the compiler accepts
    for load, store, RMW and `cmpxchg`; `bool`, enum, pointer, `f32` and `f64` cells; and three
    threaded litmus tests with a deterministic outcome on a conforming target (message passing
    with release/acquire: no stale read in 100000 rounds; store buffering with `seq_cst`: never
    both zero; four threads adding to `u8`, `u24`, `u128` and a `cmpxchgWeak` loop on `u64`: the
    exact sum). A relaxed litmus test is not recorded, because its outcome is not deterministic.
- L09's `tests/roadmap/vector-layouts/probe.zig`: bit-packed vector sizes, alignments and
  memory images.
- `tests/roadmap/aarch64-abi/limits/*.zig`: programs the compiler must reject, one `limit` row
  each with the first compile error. `atomic_u256` (a `u256` `@atomicRmw`: "expected 128-bit
  integer type or smaller") records the widest atomic integer. The others record the
  boundaries of the memory orderings (a `release` load, an `acquire` store, an `unordered` RMW,
  a `cmpxchg` whose failure ordering is stronger than its success ordering or is `release`) and
  of the cell types (an array or a vector; `Add` on a `bool`; `And` on a float). An atomic
  `f80` is not listed: Zig 0.16.0 and 0.15.2 hand the module to LLVM, which aborts on it.

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

These results differ from the model on **both** profiles (and on every recorded Zig version). `Model.lean` lists them. It
prints each one as a divergence and never counts it as a match. It fails if a listed case
starts to match (the list is stale) or if an unlisted case diverges.

| Case | aarch64 (both) | Model / x86_64 reference |
| --- | --- | --- |
| `isnan(f80 unnormal)` | `false`: compiler_rt soft f80 treats it as a number | `true` (x87 and `Float.classify`) |
| `f80 pseudo-denormal + 0` | encoding kept (`0000_8000…`) | normalized (`0001_8000…`) |
| `u24` cmpxchg, padding byte `ff` | **fails**, although the 24-bit values are equal | succeeds |
| `u40` cmpxchg, padding bytes `ff` | **fails**, although the 40-bit values are equal | succeeds |
| `i24` and `i40` `@atomicRmw` `Max`, negative cell and positive operand | **keeps the negative cell**: not the signed maximum | the signed maximum |

The model allows `unnormal + 0` itself, because it classifies the returned unnormal as a NaN.
The divergence shows up in `isnan`.

Zig 0.14.1 and 0.15.2 have two more divergences, on both profiles. Their soft-float `@sqrt`
of `f80` and `f128` is correct to `f64` precision only (`sqrt(2)` = `3fff b504f333f9de68 00…` for
`f80`, where 0.16.0 gives `…de6484`), so the correctly rounded model disagrees. `Model.lean`
lists them for those versions only; otherwise the 0.15.2 and 0.14.1 files equal the 0.16.0
files line for line (apart from `meta zig`).

The signed `Max` row is an unsound corner of the model: the model's `RmwOp.apply` is the
signed maximum, and the native result of a padded signed width (`i24`, `i40`) is not. `Min` and
the unpadded widths (`i8`, `i64`, `i128`) agree. The translator rejects `.Max` and `.Min` on a
padded width (`CheckCtx.checkPaddedAtomic`, diagnostic `PADDED_ATOMIC`).

The cmpxchg rows are a synchronization boundary. Zig widens a `u24`/`u40` atomic to its
4-/8-byte ABI cell and compares the whole cell, padding included. A plain store writes only
the value bytes. The model leaves padding undefined and compares only the value bits. So
the model's strong cmpxchg claim is not valid for widths with whole padding bytes (`u24`,
`u40`, `u48`, `u56`, `u65`…`u120`). The translator rejects a `cmpxchg` on them
(`PADDED_ATOMIC`). The LLVM IR that Zig 0.16.0
emits shows the mechanism: `store i40` for the plain store, and `cmpxchg ptr, i64, i64` for
the atomic. The widening comes from Zig's frontend lowering, so other targets probably behave
the same way. This has been observed only on aarch64. Widths without padding (`u8`,
`u16`, `u32`, `u64`, `u128`) match on both profiles, with either padding.

### Zig 0.17.0

The 0.17.0 files (recorded with the stock 0.17.0: natively on Apple silicon, and in a
`linux/arm64` container) differ from 0.16.0's in four ways, on both profiles unless noted:

| Row | 0.17.0 | Model |
| --- | --- | --- |
| `float f80` (and `float f128` on aarch64-macos-none, where it is not `c_longdouble`) | alignment 8 | 16 |
| `vector f80x2` | alignment 8; the second lane's image is not `Vec.packedEnc`'s | 32, bit-packed |
| `atomic u24`/`u40` `padff` | cmpxchg succeeds | succeeds (no longer a divergence) |
| `rmw i24`/`i40` `Max` | the signed maximum | the signed maximum (no longer a divergence) |

`Model.lean` declares the layout rows as 0.17.0 divergences (`layoutDivergences017`): the file
must record alignment 8 there and the model's table elsewhere, and the CI step compares the
vector images without `f80x2` (`vector-layouts/Model.lean --skip f80x2`). The translator rejects
these types in memory on 0.17.0: `checkMemTy` compares the exporter's alignment with the model's.
The padded `cmpxchg` and `.Max`/`.Min` stay rejected on every version. Only the two soft-float
`f80` rows remain result divergences in 0.17.0.

## Per-profile observations (every recorded Zig version, ReleaseSafe)

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

## Translation

Each profile's facts are a row of `Target.qualified`: 64-bit little-endian pointers, the
integer and float layouts of `Zig.intSize`/`Zig.intAlign` (the layout tables above),
`c_longdouble` (`f128` on aarch64-linux-gnu, `f64` on aarch64-macos-none), the float rules
(`FloatRules.aarch64`, premise MTH-04, [floats.md](floats.md#targets)) and 128-bit atomics. The
two rows differ in `c_longdouble` and in `f16` `@mulAdd`: `apple_m1` has `fullfp16` and fuses it,
the aarch64-linux `generic` CPU rounds it through `f32`. Both differ from x86_64 in `f80` (soft
float) and in `f32`/`f64` `@mulAdd` (fused). The declared divergences above stay outside every
translation: a noncanonical `f80` operand is `.unspecified`, the pre-0.16.0 `@sqrt` is the
`f64`-precision helper, and a padded `cmpxchg` or `.Max`/`.Min` is rejected.

The examples are translated, built and differentially tested natively on both hosts
(`scripts/check.sh`); aarch64-linux AIR differs from the x86_64-linux goldens only where
`tests/golden/<version>/<ex>/air-linux-aarch64/` and `Gen-linux-aarch64.lean` say so.

## Scope

Not covered:

- other modes (ReleaseFast: [build-modes.md](build-modes.md));
- `compiler-rt` float mode, libm and the float operations not listed above;
- vector float arithmetic;
- weak orderings (`monotonic` message passing, relaxed store buffering): outcomes are
  allowed, not forced, so nothing deterministic can be recorded; the model's weak-memory
  semantics is in `ZigLean/Conc/WeakCas.lean` (`docs/weak-cas.md`);
- instruction-level ordering strength (LDAR/STLR vs LL/SC) and futex/mutex behaviour;
- atomics on `f80`, and the `-mcpu` features other than `baseline`;
- other Zig versions. A new version needs its own `expected/<version>/` files; without them
  `compare` reports `excluded`, and the translator rejects its aarch64 AIR;
- programs linked with libc on aarch64-linux: `f128` `long double` libcalls then resolve to
  glibc, not compiler_rt. The translator rejects those `f128` ops unless `--assume-no-libc`
  ([floats.md](floats.md#targets)); a `link_libc` profile fact is a follow-up.
