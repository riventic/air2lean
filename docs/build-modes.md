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
| ReleaseSafe | **qualified**: analyzed-AIR model (PRF-02, SEM-01, TRU-02, TRU-03), plus native runs | unqualified: backend divergences |
| ReleaseFast | **qualified** (no illegal behaviour transfers), exception: float `@divExact` | unqualified: backend divergences and the exception |
| ReleaseSmall | **qualified** (as ReleaseFast), exception: float `@divExact` | unqualified: no completed run |
| Debug | **qualified**: tested-input agreement | unqualified: backend divergences |

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
inputs, and ReleaseFast AIR is never translated. The premise does not cover code under
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
The records state this as an exception of the premise.

**Debug/llvm** keeps the safety checks. It is qualified only as agreement on the tested
inputs, including safety panics. Debug AIR is never exported.

**Known exceptions (open).** The premise needs the model to throw on every illegal behaviour
that ReleaseSafe does not check. The memory-model audit
([architecture-audit/memory-model.md](architecture-audit/memory-model.md), MM-7) found illegal
behaviour without a model throw, so "the ReleaseSafe model does not throw" does not yet imply
"no illegal behaviour" for programs that do any of the following:

- **Observe addresses** (MM-1, MM-2). Blocks sit at a fixed, deterministic model layout.
  `@intFromPtr`, pointer order and the address-dependent safety checks (`@alignCast`, the
  alignment check of `@ptrFromInt`) are decided by that layout, not by the native one. A model
  run can pass an alignment check that panics natively, or the reverse.
- **Overflow the stack** (MM-5). The model has no stack bound; deep recursion or large frames
  return normally in the model and crash natively.
- **Use a float `@divExact` with an inexact quotient.** The ReleaseSafe check only catches a NaN
  quotient, so the model returns a value (being fixed on `codex/fix-unchecked-illegal`).

The premise holds only for programs that do none of these. Each item is lifted when its fix
lands.

**Fixed.** Forming a pointer outside its allocation (MM-3): LLVM lowers `ptr_add`, `ptr_sub`,
element, field and `@fieldParentPtr` pointers to `getelementptr inbounds`, and a result outside
`[base, base+size]` of the allocation is poison. Generated code now forms these pointers with
`Zig.ptrProject`, which throws `.illegal` there (offset 0 is always allowed). Residual: the
payload pointer of a pointer-form `try` and of `errunion_payload_ptr_set`
(`Zig.tryPayloadPtr`, `Zig.errSetOk`) is formed after a checked access to the error code but
not bounds-checked itself; it leaves the allocation only for an error union pointer that
addresses a truncated object (a pointer cast), and every access through it is still checked.

`scripts/diff.sh` also builds its libm and asm helper archives with `-OReleaseFast`,
as Zig builds compiler_rt. These are test oracles, not a claimed program build.

## Native runs

`AIR2LEAN_DIFF_OPTIMIZE` and `AIR2LEAN_DIFF_BACKEND` make `scripts/diff.sh` build the
native harness in another mode or backend (`-fllvm`, `-fno-llvm`). The model side is
unchanged, so every run compares native behaviour with the ReleaseSafe model. In
ReleaseFast and ReleaseSmall the safety checks are gone: an input on which the model
throws is illegal behaviour, so it is counted as `ub_excluded` and not compared. Rows for
which the harness cannot render the result of such a call count the same way.
`python3 scripts/build-modes.py record` writes one record per
(version, target, mode, backend) to [`assurance/build-mode-runs/`](../assurance/build-mode-runs/).
A record has the case count, the count of every outcome, each exclusion by function, the
triaged mismatches with a reproducer, and the examples left out. `scripts/build-mode-docker.sh`
runs the x86_64-linux pairs in the pinned linux/amd64 local-CI image (emulated on an arm64
host; the harness is linked with `-z norelro` because Rosetta rejects the empty RELRO
segment of release builds).

Zig 0.16.0 (stock), 85884 cases per aarch64-macos run and 87084 per x86_64-linux run (emulated). The
x86_64-linux Debug, ReleaseFast and ReleaseSmall LLVM records were re-recorded from the native CI
run after batches 7-8 added examples (87409 cases, the same mismatches and exclusions); CI uploads
those summaries (`build-mode-summaries-*`) and verifies the records on every run.

| Target | Mode | Backend | Mismatches | `ub_excluded` |
| --- | --- | --- | --- | --- |
| aarch64-macos | ReleaseSafe, Debug | llvm | 0 | 0 |
| aarch64-macos | ReleaseFast, ReleaseSmall | llvm | 85 (float `@divExact`) | 4975 |
| x86_64-linux | ReleaseSafe, Debug | llvm | 0 | 0 |
| x86_64-linux | ReleaseFast, ReleaseSmall | llvm | 85 (float `@divExact`) | 4975 |
| x86_64-linux | ReleaseSafe, Debug | stage2_x86_64 | 521 | 0 |
| x86_64-linux | ReleaseFast | stage2_x86_64 | 606 | 4975 |
| x86_64-linux | ReleaseSmall | stage2_x86_64 | no run | |

The aarch64-macos runs count 760 float results as `host_difference` (the float model
follows x86_64-linux, `host.txt`); the x86_64-linux runs have none. No aarch64-linux run
exists yet.

**stage2_x86_64 findings.** The self-hosted backend disagrees with the LLVM backend and the
model on legal inputs, in every optimize mode
([`stage2-x86_64-divergences.zig`](../tests/roadmap/build-modes/reproducers/stage2-x86_64-divergences.zig)):

- float `@mod` with operands of opposite sign, 346 cases. LLVM computes
  `frem(frem(a, b) + b, b)` and the model follows it; the backend rounds differently;
- an `i4` read from a packed union and returned is not sign-extended, 173 cases;
- f80 `@min` and `@max` of signed zeros, 2 cases. The language leaves the order open, so
  this may be a model over-specification.

`examples/asm` does not compile with `-fno-llvm -mcpu=baseline` (the backend cannot encode
the `lzcnt` and `popcnt` inline asm), so it is excluded from these runs. The ReleaseSmall
`-fno-llvm` harness binaries die with SIGBUS at start under the emulated container. That
cannot be told from an emulator problem, so the pair has no run.

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

To qualify a stage2_x86_64 pair, fix or model the findings, then rerun the pair on a
native x86_64-linux host.
