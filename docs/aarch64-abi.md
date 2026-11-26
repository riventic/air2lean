# aarch64 ABI qualification (T04)

Two aarch64 profiles are qualified separately: **aarch64-linux-gnu** (`-mcpu=baseline` =
`generic`) and **aarch64-macos-none** (`-mcpu=baseline` = `apple_m1`). Both use stock Zig
(0.17.1, 0.16.0, 0.15.2 and 0.14.1, each with its own expected file), the LLVM backend and
ReleaseSafe. Each profile has three pieces of evidence:

1. A native probe run. `scripts/aarch64-abi.py` runs only on the profile's own host. It does
   not use an emulator or cross execution.
2. A versioned expected file. The probe output must equal it line for line.
3. A Lean check tied to that file. Kernel-checked layout tables are compared with the file, and
   the recorded results are compared with the model.

The translator accepts both profiles (`Target.qualified` in `Air2Lean/Air/Dialect.lean`;
[profiles.md](profiles.md#aarch64-abi-profiles-t04)). aarch64-linux only for the Zig versions
with an expected file (`Target.aarch64Probed`: 0.17.1, 0.16.0, 0.15.2 and 0.14.1, on both
profiles) and, on aarch64-linux, the `gnu` ABI: any other is a profile error.
See [target-matrix.md](target-matrix.md) and §Translation below.

```sh
# On the profile's host (aarch64 Linux or Apple silicon macOS), with a stock Zig whose version
# has an expected file (0.17.1, 0.16.0, 0.15.2, 0.14.1):
python3 scripts/aarch64-abi.py check --zig /path/to/zig --target aarch64-linux-gnu
python3 scripts/aarch64-abi.py check --zig /path/to/zig --target aarch64-macos-none
# Any host:
python3 scripts/aarch64-abi.py compare --target aarch64-linux-gnu OBSERVED.txt
lake build ZigLean.VecMem ZigLean.Float.Allowed ZigLean.Mem.Thread ZigLean.Os ZigLean.Conc.Sched
lake env lean --run tests/roadmap/aarch64-abi/Model.lean aarch64-linux-gnu \
  tests/roadmap/aarch64-abi/expected/0.16.0/aarch64-linux-gnu-ReleaseSafe.txt
lake env lean --run tests/roadmap/aarch64-abi/Futex.lean aarch64-linux-gnu \
  tests/roadmap/aarch64-abi/expected/0.16.0/aarch64-linux-gnu-ReleaseSafe.txt
python3 -m unittest discover -s tests/roadmap/aarch64-abi -p 'test_*.py'
python3 tests/roadmap/aarch64-abi/test_float_atomics.py .lake/build/bin/air2lean
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
    exact sum). A relaxed litmus test is not recorded, because its outcome is not deterministic;
  - the `futex` rows of `tests/roadmap/aarch64-abi/futex.zig` (§Futex).
- L09's `tests/roadmap/vector-layouts/probe.zig`: bit-packed vector sizes, alignments and
  memory images.
- `tests/roadmap/aarch64-abi/limits/*.zig`: programs the compiler must reject, one `limit` row
  each with the first compile error. `atomic_u256` (a `u256` `@atomicRmw`: "expected 128-bit
  integer type or smaller") records the widest atomic integer. The others record the
  boundaries of the memory orderings (a `release` load, an `acquire` store, an `unordered` RMW,
  a `cmpxchg` whose failure ordering is stronger than its success ordering or is `release`) and
  of the cell types (an array or a vector; `Add` on a `bool`; `And` on a float).
- `tests/roadmap/aarch64-abi/atomic_f80.zig`, built once per atomic op on an `f80` cell (load
  and store at each ordering, RMW `.Xchg`/`.Add`/`.Sub`/`.Max`/`.Min`, `cmpxchg` strong and
  weak; `F80_OPS`): one `f80atomic` row each with Sema's error (`zig`), the LLVM backend's
  error (`llvm`), or, if it runs, whether the cell and the returned value are those of the op
  without atomics (`runs cell=model|other result=model|other`). See §Atomic `f80`.

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

The model allows `unnormal + 0` itself, because it classifies the returned unnormal as a NaN.
The divergence shows up in `isnan`.

Zig 0.14.1 and 0.15.2 have two more divergences, on both profiles. Their soft-float `@sqrt`
of `f80` and `f128` is correct to `f64` precision only (`sqrt(2)` = `3fff b504f333f9de68 00…` for
`f80`, where 0.16.0 gives `…de6484`), so the correctly rounded model disagrees. `Model.lean`
lists them for those versions only; otherwise the 0.15.2 and 0.14.1 files equal the 0.16.0
files line for line (apart from `meta zig`).

### Padded-width atomics: rejected, not declared

A `cmpxchg` or an `@atomicRmw` `.Max`/`.Min` on an integer representation with padding bits
(bit width other than `8 * @sizeOf`: `u7`, `i12`, `u24`, `i40`, an `enum(u24)`, a packed struct
backed by `u40`) is outside the subset on every target and version: the translator rejects it
(`CheckCtx.checkPaddedAtomic`, diagnostic `PADDED_ATOMIC`,
[upstream draft](upstream/padded-rmw-minmax.md)). Zig lowers these to an LLVM atomic on the whole
ABI cell, so the padding bits take part: a `cmpxchg` fails on equal values when the padding is
not what the compiler expects, and a signed `.Max`/`.Min` orders a negative cell as a large
unsigned value. Loads, stores, `.Xchg` and the arithmetic and bitwise RMWs stay in the subset:
their results are masked, and they only write the padding, which the model leaves undefined.

`Model.lean` therefore does not declare these rows. A diverging result line is accepted, and
printed as `rejected by the translator (PADDED_ATOMIC, not a match)`, only when it is a
`cmpxchg` or `.Max`/`.Min` of a padded type (`rejectedByTranslator`); for an `atomic` row, only
its `cmpxchg` may differ, and every later result must follow from the cell the failed
`cmpxchg` left (`paddedAtomicCase`). Any other divergence of an atomic row fails the check. Up to
0.16.0 the `atomic u24`/`u40` `padff` rows (cmpxchg with padding byte `ff`) and the
`rmw i24`/`i40` `Max` rows (negative cell, positive operand) diverge on both profiles, and are
classified this way.

A wider native probe (Zig 0.14.1 to 0.17.1 on aarch64-macos) shows that the rule must cover every
padded width, not only whole padding bytes: on 0.14.1 to 0.16.0 a signed `.Max` diverges for
`i7`, `i12`, `i40`, `i48` and `i56` as well, an unsigned `.Min` for `u24`, `u48` and `u56`, a
`cmpxchg` with `ff` padding for `u24` to `u56`, and on every version including 0.17.1 a
`cmpxchg` after an `.Add` that carried into the padding fails for `u7`, `u12`, `u24`, `u40`,
`u48` and `u56`. All of these are padded `cmpxchg`/`.Max`/`.Min` operations, which the translator
rejects; widths without padding (`u8` to `u64`, `i8` to `i64`) agree with the model everywhere.

### Atomic `f80`

The model has no float atomic messages, and the translator rejects every atomic op on a float
cell on every target and version (`CheckCtx.atomicChild`: "a float atomic is outside the
subset"; on 0.17.1 aarch64 the `f80` cell's alignment is rejected first, see below, and an `f80`
`.Max`/`.Min` is `PADDED_ATOMIC`). The `f80atomic` rows show that nothing weaker would be sound.
On both profiles:

| Op | 0.14.1, 0.15.2, 0.16.0 | 0.17.1 |
| --- | --- | --- |
| `@atomicLoad` (each ordering), `@atomicRmw` `.Add`/`.Sub`/`.Max`/`.Min` | LLVM: `Broken module found` | the same |
| `@atomicRmw` `.Xchg` | LLVM: `Invalid cast` | the same |
| `@atomicStore` (each ordering) | LLVM: `Broken module found` | **runs, the cell is not the operand** |
| `@cmpxchgStrong`/`@cmpxchgWeak` | Sema: `expected bool, integer, enum, packed struct, or pointer type; found 'f80'` | the same |

0.17.1 lowers `@atomicStore(f80, p, v, …)` to `store atomic ptr <v's address>, ptr p`: the cell's
low eight bytes become an address (different on each run) and its high bytes keep the old value
([upstream draft](upstream/f80-atomic-store.md)). `Model.lean` prints each `f80atomic` row as
rejected by the translator, never as a match, and fails on a missing or malformed row;
`test_float_atomics.py` runs the translator on AIR fixtures with each recorded version's
aarch64-linux-gnu and aarch64-macos-none profile and checks that every float width (`f16` to
`f128`) and every atomic op that reaches AIR is rejected with its diagnostic and leaves the
output untouched, while the same ops on a `u32` cell are accepted.

### Futex

The model's kernel wait queue is two trusted OS rows per target (`ZigLean/Os/Futex.lean`,
premises [OSF-01 and OSF-02](premises.md#osf-01)): `futex_4arg`/`futex_3arg` on Linux and
`__ulock_wait2`/`__ulock_wait`/`__ulock_wake` on macOS. Their sources are the kernels' code;
`futex.zig` observes the same calls natively on each aarch64 profile, and
`tests/roadmap/aarch64-abi/Futex.lean` checks every `futex <case> <value>` row against the rows.

For each case `Futex.lean` runs the model's row on the same arguments under the scheduler
(`Zig.Sched.runTrace`), over every schedule and every choice of the oracle, and collects the
results. A choice among more than four options (the `2^31 + 1` results of a macOS wait) is cut
to its first four, which only removes outcomes. The native value must be one of these outcomes.
The check fails on a missing, repeated, unknown or malformed row and on a file of the other
profile. `Model.lean` requires the profile's number of `futex` rows (79 on aarch64-linux-gnu,
35 on aarch64-macos-none). When `Futex.lean` is elaborated, it checks that no case's run stops
at its cap of 4000 schedules, and that the model excludes a list of values (`forbidden`: a wake
above its limit, a wake of a sleeper in the other domain, a success where the kernel must
fail).

A value is a return code as a signed decimal (`-errno` on failure). On the std wrappers: the
probe calls the wrapper that the translator binds (`futex_4arg`/`futex_3arg`;
`futex_wait`/`futex_wake` on 0.14.1) wherever its pointer type can carry the address, and the
raw system call for a null address and, on 0.14.1, for an unaligned one. The rows are the same
for all four Zig versions.

**aarch64-linux-gnu**, each case with `FUTEX_PRIVATE_FLAG` and without (the word is on a stack:
anonymous memory, as a shared key needs it in the model):

| Case | Native | Model |
| --- | --- | --- |
| WAIT, word ≠ expected, with and without a timeout | `-EAGAIN` | the same |
| WAIT, word = expected, timeout 1 ms or 0 | `-ETIMEDOUT` | `-ETIMEDOUT` or `-EINTR` |
| WAIT, timeout with `nsec = 10^9`, `nsec < 0` or `sec < 0`; also with a mismatch, an unaligned address or a kernel address | `-EINVAL` | the same (the timeout is validated first) |
| WAIT or WAKE, address not a multiple of 4, also a kernel address | `-EINVAL` | the same (alignment before the address) |
| WAIT or WAKE, address with bits 63 and 55 set, and `2^64 - 4` | `-EFAULT` | the same |
| WAKE with nobody asleep, `val` 1, 0 and `2^31 - 1` | 0 | the same |
| private WAKE at address 0 | 0 | the same (a private key needs no page) |
| one sleeper, WAKE with `val` 1, 2, 0, `2^31 - 1`, `0xffffffff`; the sleeper private, shared, or with a 60 s timeout | the wake returns 1, the wait 0 | among the outcomes |
| three sleepers, `val` 1, 0, `0xffffffff` | three non-zero returns, each 1 | the same (`Linux.wakeLimit`: `val ≤ 0` wakes one) |
| three sleepers, `val` 2 and `2^31 - 1` | the returns sum to 3, none above `val` | the same |
| a shared sleeper and a private WAKE of all, and the reverse | 0, then the sleeper's own domain wakes it | the same (the key has the domain) |

**aarch64-macos-none**, `__ulock_wait2` and `__ulock_wait` with `COMPARE_AND_WAIT | NO_ERRNO`,
`__ulock_wake` with and without `WAKE_ALL`:

| Case | Native | Model |
| --- | --- | --- |
| wait, word ≠ expected, with and without a timeout | 0 (`--ull_nwaiters`) | `-EFAULT` or any non-negative code |
| wait, word = expected, timeout 1 ms | `-ETIMEDOUT` | `-ETIMEDOUT` or `-EINTR` |
| wait, null or unaligned address | `-EINVAL` | the same |
| wake, null address | `-EINVAL` | the same |
| wake with nobody asleep; at an unaligned or unmapped address | `-ENOENT` | `-ENOENT`, 0 or `-EINTR` |
| one sleeper (either wait call, with or without a timeout), wake of one or all | the wake returns 0, the wait 0 | among the outcomes |
| three sleepers, wake of one, each after the last woken waiter returned | three successes; every wait returns a non-negative code | among the outcomes |
| three sleepers, `WAKE_ALL` | only successes; every wait returns a non-negative code | among the outcomes |

Both profiles also record `futex mutex 4x20000=80000`: four threads take a lock built on the
two calls alone (Drepper's three-state mutex) 20 000 times each around a plain counter. No
increment is lost and the run ends. `Futex.lean` checks the product, as `Model.lean` does for
the `litmus counters` row: it is a native observation of the calls under contention. Beside
it, `Futex.lean` runs the same lock on the model's Linux rows, two threads and one round each,
over every schedule (`Lock.run`, checked at elaboration): the counter is 2 in every run that
ends, and no run is a data race on the counter or a deadlock. On the macOS rows the schedules
are too many for that check. There the model's `__ulock_wake` may return `-EINTR` with nobody
woken (a conservative extra outcome: xnu's wake path never does), so a lock that does not
repeat such a wake can deadlock in the model; the probe's lock repeats it, as std does.

Thirteen calls are **refused by the model**: it says `.illegal` where the kernel returns
`-EFAULT`, the conservative refusal of an address that is not a live word of the model and
whose native result needs mapping or address-space knowledge (OSF-01/OSF-02, "Model gaps").
`Futex.lean` prints each as `refused by the model (.illegal, not a match)`, requires that the
model still refuses it, and never counts it as a match:

| Case | Native |
| --- | --- |
| Linux WAIT at address 0, private and shared | `-EFAULT` |
| Linux shared WAKE at address 0 | `-EFAULT` |
| Linux WAIT and WAKE, private and shared, at the word's address with a top-byte tag (bit 56; the process has not enabled the tagged-address ABI) | `-EFAULT` |
| Linux WAIT and WAKE, private and shared, at the word's address with bit 63 set | `-EFAULT` |
| macOS `__ulock_wait2` and `__ulock_wait` at an unmapped address (8) | `-EFAULT` |

Every row is the same on every run, so the rows are part of the expected file. A threaded case
records only what does not depend on when its sleepers fall asleep: the waker repeats its call
until every waiter has returned, and with three sleepers the returns are recorded only where
each one is forced (a limit of one), else their sum. A case that does not end within 10 s
prints `stuck`, which is a mismatch.

Not probed: `EINTR` (the probe sends no signal); a shared key on a file-backed page (the model
refuses it); how a wake above one splits over sleepers that are all asleep (the probe cannot
know when a thread sleeps); `os_unfair_lock` and the `EDOM` gap at a `std.Thread.Mutex` word
(STD-06, [audit S6 finding 4](architecture-audit/soundness-2026-10-14.md)); `std.Thread.Futex`,
`std.Thread.Mutex` and `Io.Threaded`, which are translated std code over these rows.

### Zig 0.17.1

The 0.17.1 files (recorded with the stock 0.17.1: natively on Apple silicon, and in a
`linux/arm64` container) differ from 0.16.0's in four ways, on both profiles unless noted:

| Row | 0.17.1 | Model |
| --- | --- | --- |
| `float f80` (and `float f128` on aarch64-macos-none, where it is not `c_longdouble`) | alignment 8 | 16 |
| `vector f80x2` | alignment 8; the second lane's image is not `Vec.packedEnc`'s | 32, bit-packed |
| `atomic u24`/`u40` `padff` | cmpxchg succeeds | succeeds (no padded-width row diverges) |
| `rmw i24`/`i40` `Max` | the signed maximum | the signed maximum |

`Model.lean` declares the layout rows as 0.17.1 divergences (`layoutDivergences017`): the file
must record alignment 8 there and the model's table elsewhere, and the CI step compares the
vector images without `f80x2` (`vector-layouts/Model.lean --skip f80x2`). The translator rejects
these types in memory on 0.17.1: `checkMemTy` compares the exporter's alignment with the model's.
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
- instruction-level ordering strength (LDAR/STLR vs LL/SC);
- the futex cases listed as not probed in §Futex;
- the `-mcpu` features other than `baseline`;
- other Zig versions. A new version needs its own `expected/<version>/` files; without them
  `compare` reports `excluded`, and the translator rejects its aarch64 AIR;
- programs linked with libc on aarch64-linux: `f128` `long double` libcalls then resolve to
  glibc, not compiler_rt. The translator rejects those `f128` ops unless `--assume-no-libc`
  ([floats.md](floats.md#targets)); a `link_libc` profile fact is a follow-up.
