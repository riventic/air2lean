# Build-mode and backend qualification

[`assurance/build-modes.json`](../assurance/build-modes.json) has one qualification
record for each optimize mode (`Debug`, `ReleaseSafe`, `ReleaseFast`, `ReleaseSmall`)
and backend (`llvm`, `stage2_x86_64`). A record is `qualified`, `unqualified` or
`excluded`. It also names the claim it supports, the premise that relates the safe
analyzed AIR to that build, the premise IDs from [premises.md](premises.md), and the
evidence. A qualification is evidence for a stated premise. It is not a backend
preservation theorem.

## Shipping build

| Step | Compiler | Flags | Source |
| --- | --- | --- | --- |
| AIR export | patched Zig ([zig-patch](../zig-patch/README.md)) | `build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing` | `scripts/check.sh`, `scripts/translate.sh` |
| Native differential harness | stock Zig, same version | `build-exe -OReleaseSafe -mcpu=baseline` | `scripts/diff.sh` |

Every committed schema-12 export records `backend: stage2_llvm` and
`build_mode: ReleaseSafe`. `compatibility.json` names `ReleaseSafe` as the translation
optimize mode. The differential harness relies on Zig's default LLVM backend for
release modes. It passes no backend flag.

## Records

| Mode | `llvm` | `stage2_x86_64` |
| --- | --- | --- |
| ReleaseSafe | **qualified**: analyzed-AIR model (PRF-02, SEM-01, TRU-02, TRU-03), plus native runs | **qualified**: tested-input agreement of its own translation (x86_64-linux) |
| ReleaseFast | **qualified** (no illegal behaviour transfers), exception: float `@divExact` | **qualified** (no illegal behaviour transfers, x86_64-linux) |
| ReleaseSmall | **qualified** (as ReleaseFast), exception: float `@divExact` | unqualified: no completed run |
| Debug | **qualified**: tested-input agreement | **qualified**: tested-input agreement (x86_64-linux) |

**ReleaseSafe/llvm** is the reference build. Proofs concern its analyzed AIR. A golden
export, the ABI-probe profiles and the export and harness commands are the evidence.
Native behaviour is related to the model only by the bounded differential tests and ABI
probes (TRU-03).

**ReleaseFast and ReleaseSmall (llvm) premise.** They compile the same source and only
remove safety checks. They can therefore diverge from ReleaseSafe only on executions that
have illegal behaviour. If the ReleaseSafe model does not throw on an input, the source has
no illegal behaviour on that input. This holds only if export, translation and LLVM
lowering are faithful (TRU-02, TRU-03). This is the premise behind the README sentence on
ReleaseFast. No output, layout or performance correspondence is claimed beyond the tested
inputs, and ReleaseFast AIR is never translated by default: the translator admits only the
qualified `ReleaseSafe`/`stage2_llvm` profile unless `--allow-unqualified-build-mode` is
given, and that opt-in is recorded in the generated header (`docs/air-json.md` §Schema
table). The premise does not cover code under
`@setRuntimeSafety(false)` or `@setFloatMode(.optimized)`. It also does not cover other
CPU features, other error-tracing settings, or comptime branches on
`@import("builtin").mode`.

**Exception: float `@divExact`.** ReleaseSafe does not check that a float `@divExact` is
exact. The model returns the truncated quotient without throwing, and so does the
ReleaseSafe and Debug build. ReleaseFast and ReleaseSmall return the plain quotient. The
differential runs show 85 such cases (`floatops.divExact64`, every input with a
non-integral quotient). For a function that uses float `@divExact`, "the model does not
throw" does not imply "no illegal behaviour", so the transfer claim does not apply to it.
The reproducer is
[`float-divexact-inexact.zig`](../tests/roadmap/build-modes/reproducers/float-divexact-inexact.zig).
The records state this as an exception of the premise. The model now returns `.illegal` for
an inexact float `@divExact` quotient, so no run records a mismatch for it (the 85 cases are
`illegal_exclusion`).

**Debug/llvm** keeps the safety checks. It is qualified only as agreement on the tested
inputs, including safety panics. Debug AIR is never exported.

**Known exceptions.** The premise needs the model to throw on every illegal behaviour that
ReleaseSafe does not check. The memory-model audit
([architecture-audit/memory-model.md](architecture-audit/memory-model.md), MM-7) found one such
gap, now closed: an inexact float `@divExact` quotient, which the ReleaseSafe check catches only
when it is NaN, is `.illegal` in the model ([illegal-behavior.md](illegal-behavior.md)), and the
re-recorded runs of all three targets record it as `illegal_exclusion`, with no mismatch.

**Fixed.** Address observation (MM-1, MM-2): every block's address is the environment's
placement (`Mem.place`, premise SEM-07), and generated theorems hold for every placement, so a
no-throw proof covers the native layout, including the address-dependent safety checks
(`@alignCast`, the alignment check of `@ptrFromInt`). Stack overflow (MM-5): a recursive function
that uses memory charges its frame to the stack budget `Mem.stackLimit` and throws
`.stackOverflow` when it does not fit; a statement without a budget assumes that the native stack
holds every call chain (premise STK-01), which the claim tooling lists for such a goal.

Forming a pointer outside its allocation (MM-3): LLVM lowers `ptr_add`, `ptr_sub`,
element, field and `@fieldParentPtr` pointers to `getelementptr inbounds`, and a result outside
`[base, base+size]` of the allocation is poison. Generated code now forms these pointers with
`Zig.ptrProject`, which throws `.illegal` there (offset 0 is always allowed). This includes
the payload pointer of a pointer-form `try` and of `errunion_payload_ptr_set`
(`Zig.tryPayloadPtr`, `Zig.errSetOk`).

`scripts/diff.sh` also builds its libm and asm helper archives with `-OReleaseFast`,
as Zig builds compiler_rt. These are test oracles, not a claimed program build.

## Native runs

`AIR2LEAN_DIFF_OPTIMIZE` and `AIR2LEAN_DIFF_BACKEND` make `scripts/diff.sh` build the
native harness in another mode or backend (`-fllvm`, `-fno-llvm`). The model side is
unchanged, so every run compares native behaviour with the ReleaseSafe model. In
ReleaseFast and ReleaseSmall the safety checks are gone: an input on which the model
throws is illegal behaviour, so it is counted as `ub_excluded` and not compared. Rows for
which the harness cannot render the result of such a call count the same way, and so do those
of an input pinned illegal (`illegal_exclusion`, e.g. a slice formed outside its allocation).
`python3 scripts/build-modes.py record` writes one record per
(version, target, mode, backend) to [`assurance/build-mode-runs/`](../assurance/build-mode-runs/).
A record has the case count, the count of every outcome, each exclusion by function, the
triaged mismatches with a reproducer, and the examples left out. `scripts/build-mode-docker.sh`
runs the x86_64-linux pairs in the pinned linux/amd64 local-CI image (emulated on an arm64
host; under Rosetta the harness is linked with `-z norelro`, see [rosetta.md](rosetta.md)).

Zig 0.16.0 (stock), 86209 cases per aarch64-macos and aarch64-linux run (each host's own
translations, `scripts/check-tree.py create --host-goldens 0.16.0`) and 87084 per x86_64-linux run (emulated). The
x86_64-linux Debug, ReleaseFast and ReleaseSmall LLVM records were re-recorded from the native CI
run after batches 7-8 added examples (87409 cases), and again after the soundness batch (87413
cases: four asm fault inputs; inexact float `@divExact`, MM-3 out-of-bounds pointers and the
`@fieldParentPtr` cases are pinned illegal, so the 85 float `@divExact` mismatches are now
`illegal_exclusion`); CI uploads those summaries (`build-mode-summaries-*`) and verifies the
records on every run.

| Target | Mode | Backend | Mismatches | `ub_excluded` |
| --- | --- | --- | --- | --- |
| aarch64-macos | ReleaseSafe, Debug | llvm | 0 | 0 |
| aarch64-macos | ReleaseFast, ReleaseSmall | llvm | 0 | 4922 |
| aarch64-linux | ReleaseSafe, Debug | llvm | 0 | 0 |
| aarch64-linux | ReleaseFast, ReleaseSmall | llvm | 0 | 4922 |
| x86_64-linux | ReleaseSafe, Debug | llvm | 0 | 0 |
| x86_64-linux | ReleaseFast, ReleaseSmall | llvm | 0 | 4922 |
| x86_64-linux | ReleaseSafe, Debug | stage2_x86_64 | 0 (34343 cases; `floatops`, `layout` rejected, `asm` not compiled) | 0 |
| x86_64-linux | ReleaseFast | stage2_x86_64 | 0 (34343 cases) | 4035 |
| x86_64-linux | ReleaseSmall | stage2_x86_64 | no run | |

No run counts a `host_difference`: each host tests its own translation, whose float rules are
that target's (`docs/floats.md` §Targets).
`examples/asm` is `host_excluded` on both aarch64 hosts.

**aarch64-linux runs.** They were recorded from `scripts/diff.sh` in a native `linux/arm64`
container (Ubuntu 24.04, stock Zig 0.16.0 `aarch64-linux`, the Lean toolchain from
`lean-toolchain`) on an Apple-silicon Docker VM: an aarch64 Linux kernel and aarch64 code, no
instruction emulation (`emulated: false`). The CI job `build-modes-aarch64-linux`
(`ubuntu-24.04-arm`, hosted hardware) re-runs all four modes against the records and
checks the case count, examples, mismatches and exclusions; its counts are the container's
(86209 cases; 4922 `ub_excluded` in ReleaseFast and ReleaseSmall, none otherwise).

The aarch64-linux runs include `floatops` and `floatconv`: they test the committed
aarch64-linux translations (`tests/golden/0.16.0/<ex>/Gen-linux-aarch64.lean`, whose float rules
the [reproducer](../tests/roadmap/build-modes/reproducers/aarch64-linux-float-targets.md)
measures natively), with that host's pins (`unspecified.Linux-aarch64.txt`). In an unchecked mode a pinned model `.illegal` (an
out-of-bounds slice pointer, MM-3) may leave a result that the harness cannot render;
`scripts/diff-report.py` counts it as `illegal_exclusion`.

**Crashing inputs and the hosted runner.** In ReleaseFast and ReleaseSmall about 700 of the
excluded inputs crash the tested call with SIGSEGV or SIGBUS (wild pointers in
`layout` and `slices`: `ptrFromAddr`, `applyOp`, `sumMid`, `sentinelArr`, `subZ`,
`copyWithin`); ReleaseSafe and Debug trap on them instead. The hosted `ubuntu-24.04-arm`
image has `kernel.core_pattern = |/usr/lib/systemd/systemd-coredump ...`, and
systemd-coredump hands each crash to apport (a Python process). The kernel starts a piped
handler even when `RLIMIT_CORE` is 0, and the crashed child is reaped without waiting for
it, so the harness went on to the next input while the handlers piled up: on the runner the
unmodified `layout` harness reached about 450 processes (many blocked in `vfs_coredump`), a
load average above 300 and all 16 GB of memory within five minutes. The runner then stopped
answering the service (the two earlier runs were lost; `timeout` killed `diff.sh` but the
step never ended). `ulimit -c 0` and stopping apport, as tried then, do not change that.
The Docker VM used for the container runs has `core_pattern = core`, so the same run took
about two minutes there. The harness (`tests/diff/common.zig`, `containChild` in
`compat.zig`) now starts every tested call as an undumpable child (`PR_SET_DUMPABLE 0` and
`RLIMIT_CORE 0`; no handler process appeared on the hosted runner with both set), caps its
address space at 4 GiB (Linux), makes it die with the harness (`PR_SET_PDEATHSIG`), and
kills it after 20 seconds. A killed case is a fatal `native_harness_failure`
(docs/outcome-accounting.md); none occurs in the recorded runs. With this, the four
LLVM modes run on the hosted runner in about 16 minutes, Lean build excluded.

**stage2_x86_64.** The self-hosted backend disagreed with the LLVM backend and the model on
legal inputs in three places
([`stage2-x86_64-divergences.zig`](../tests/roadmap/build-modes/reproducers/stage2-x86_64-divergences.zig)).
Each is now outside the subset on a `stage2_x86_64` profile, or no longer a divergence:

- **float `@mod`** with a remainder of the other sign (346 cases): the backend computes
  `r = fmod(a, b)` and adds `b` once when `r` and `b` differ in sign; the model is the LLVM
  lowering `rem(rem(a, b) + b, b)`. They differ when `r + b` rounds to `b`. The translator
  rejects a float `@mod` on a `stage2_x86_64` profile (`CheckCtx.checkStage2Backend`).
- **a signed packed-union field** narrower than a register (173 cases): a native probe
  (Zig 0.16.0 and 0.17.0; widths 1, 2, 3, 4, 7, 12, 20, 24, 33, 48 and 63 diverge, 8, 16, 32
  and 64 do not) shows that the backend does not sign-extend a signed field of a
  `packed union` whose width is not 8, 16, 32 or 64 bits (`i4` `-8` reads as `8`,
  also through `@as(i64, ...)` and `< 0`), while packed struct fields and `@bitCast` are
  correct. The translator rejects such a read (or a pointer to the field, or a signed enum
  tag field) on a `stage2_x86_64` profile.
- **f80 `@min`/`@max` of signed zeros** (2 cases): the model leaves the sign of the zero
  unspecified on every target since [PR143](https://github.com/riventic/air2lean/pull/143).

`tests/roadmap/build-modes/stage2-air/<version>/` holds the patched compilers' self-hosted
exports of the reproducer's `modF16` and `setNib` (0.16.0, 0.17.0); `stage2_rules.py` checks
that both are rejected under their profile and accepted when the profile names stage2_llvm.

A stage2_x86_64 run tests the backend's own translation. `scripts/build-mode-docker.sh` first
runs `scripts/stage2-translations.py`: each example is exported by the patched compiler with
`-fno-llvm -target x86_64-linux-gnu -mcpu=baseline` and translated under that stage2_x86_64
profile. An accepted translation must equal the committed one that the run's Lean side builds
(compared after the profile header); a different one fails the run. A rejected example (0.16.0:
`floatops`, `layout`) is left out with its diagnostics in the run record's `excluded_examples`,
as is `examples/asm`, which the backend cannot compile at `-mcpu=baseline` (it cannot encode
the `lzcnt` and `popcnt` inline asm). For every other example the stage2_x86_64 translation is
the committed translation, so the runs compare the stage2 binary with its own model.

### Fresh inputs

The committed inputs (`tests/diff/<ex>/inputs/`) are fixed: edge values plus values from one PRNG
seed (`tests/diff/input_seed.zig`). `scripts/fresh-inputs.sh SEED SUMMARY` tests other inputs: in
a check tree it writes SEED to `input_seed.zig`, regenerates the inputs with
`tests/diff/gen_inputs.zig`, and runs `scripts/diff.sh` on every example of this host whose inputs
changed. The per-input exclusion pins name the committed inputs, so in this mode
(`AIR2LEAN_DIFF_FRESH_INPUTS`, `diff-report.py --fresh-inputs`) a model `.illegal` or
`.unspecified` result is an exclusion on any input, never a match, and no pin is checked; a
value, returned-error or panic disagreement is a mismatch and fails the run. The summary records
`fresh_input_seed`, so a failure reproduces from the seed. An example with per-input pins on the
host (`unspecified.<host>.txt`, else `unspecified.txt`) is not re-tested: its pins stand for
classes where the model and the native run do not agree by value (on x86_64-linux, x87 `f80`
pseudo and invalid encodings in `floatops`; data races in `threads`), and a fresh input of such a
class has no pin (on x86_64-linux in a `linux/amd64` container, seed `0xd477d9590eede18`
gave `floatops.op80` mismatches in exactly those classes before this rule).

CI runs it on every commit of the 0.16.0 full golden row with a seed taken from the commit hash
(`Differential test on fresh inputs`), so each commit is tested on inputs no earlier commit
saw. The claim stays bounded: agreement on the inputs that were run, never on all inputs.

## Changed semantics

The records exclude these separately:

- **fast-math** (`@setFloatMode(.optimized)`): value-changing float rewrites are outside
  the IEEE and compiler-rt models (MTH-01, MTH-03). ReleaseFast does not select it.
  `*_optimized` tags are rejected by the normalizer, and the profile requires
  `float_mode: per-instruction`.
- **shipping-binary**: a profile whose `export_stage` is not `analyzed-air` is rejected.

## Check

```sh
python3 scripts/build-modes.py check
python3 -B -m unittest discover -s tests/roadmap/build-modes -v
python3 scripts/build-modes.py commands   # heavy commands still needed (Linux, stock Zig)
```

`check` needs no Zig or Lean. It requires one record for every pair. Each cited profile
must record the stated `build_mode` and backend. Each cited command must select
`-O<mode>` and the right backend and must appear in its source. A qualified record must
cite a profile and a command, or a run for each target. Premise IDs must exist. The shipping flags must appear
in their sources and agree with `compatibility.json`. Changed-semantics guards must be
present in the translator. Every paragraph in `README.md` or `docs/*.md` that names
ReleaseFast or ReleaseSmall must link this page.

`check` also validates each run record: its counts add up, only ReleaseFast and ReleaseSmall
exclude model-throwing inputs, every mismatch is triaged with an existing reproducer and
falls under an exception (qualified) or finding (unqualified) of the record, every example
left out is explained, and no tested source uses `@setFloatMode`. A qualified record needs
a run for each target it lists.

In CI, the 0.16.0 full job runs Debug, ReleaseFast and ReleaseSmall on LLVM with
`scripts/diff.sh` and `build-modes.py record --verify`, which compares the fresh run with
the committed x86_64-linux record.

