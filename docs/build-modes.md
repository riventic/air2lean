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
| ReleaseSafe | **qualified**: analyzed-AIR model (PRF-02, SEM-01, TRU-02, TRU-03) | unqualified |
| ReleaseFast | unqualified: claims only that no illegal behaviour transfers (premise below) | excluded |
| ReleaseSmall | unqualified, no claim | excluded |
| Debug | unqualified, no claim | unqualified, no claim |

**ReleaseSafe/llvm** is the reference build. Proofs concern its analyzed AIR. A golden
export, the ABI-probe profiles and the export and harness commands are the evidence.
Native behaviour is related to the model only by the bounded differential tests and ABI
probes (TRU-03).

**ReleaseFast/llvm premise.** ReleaseFast compiles the same source and only removes
safety checks. It can therefore diverge from ReleaseSafe only on executions that have
illegal behaviour. If the ReleaseSafe model does not throw on an input, the source has no
illegal behaviour on that input. This holds only if export, translation and LLVM lowering
are faithful (TRU-02, TRU-03). This is the premise behind the README sentence on
ReleaseFast. No output, layout or performance correspondence is claimed, and ReleaseFast
AIR is never translated by default: the translator admits only the qualified
`ReleaseSafe`/`stage2_llvm` profile unless `--allow-unqualified-build-mode` is given, and
that opt-in is recorded in the generated header (`docs/air-json.md` §Schema table). The premise does not cover code under
`@setRuntimeSafety(false)` or `@setFloatMode(.optimized)`. It also does not cover other
CPU features, other error-tracing settings, or comptime branches on
`@import("builtin").mode`. The record stays unqualified until a native ReleaseFast
observation exists.

`scripts/diff.sh` also builds its libm and asm helper archives with `-OReleaseFast`,
as Zig builds compiler_rt. These are test oracles, not a claimed program build.

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
cite both a profile and a command. Premise IDs must exist. The shipping flags must appear
in their sources and agree with `compatibility.json`. Changed-semantics guards must be
present in the translator. Every paragraph in `README.md` or `docs/*.md` that names
ReleaseFast or ReleaseSmall must link this page.

To qualify ReleaseFast/llvm, run the native probe pair from the record's `commands` on
the matching Linux hosts ([profiles.md](profiles.md#bounded-linux-native-abi-observations)).
A ReleaseFast differential harness build is also needed. Then commit the evidence and
update the record.
