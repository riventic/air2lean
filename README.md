# air2lean

[![CI](https://github.com/riventic/air2lean/actions/workflows/ci.yml/badge.svg)](https://github.com/riventic/air2lean/actions/workflows/ci.yml)

Translate a subset of Zig into Lean 4, then prove properties of the code in Lean.

**Status:** works for Zig 0.16.0, 0.15.2 and 0.14.1. 185 functions in 19 examples translate and match the compiled Zig on 87,121 differential tests (x86_64-linux), including the panic kind and the memory after each call. Every example has machine-checked proofs (`Proofs/`; `floatops`' `op128` without its `f128` division and `@sqrt`, which differ by Zig version). See [PLAN.md](PLAN.md).

| Examples | What they cover |
|---|---|
| `basic`, `recursion`, `options`, `errors`, `variants` | loops, mutual recursion, optionals, `try`, enums, tagged unions |
| `pointers`, `slices`, `lists` | byte-level memory, pointer aliasing, heap memory, an allocator, translated std code |
| `layout`, `vectors`, `asm` | casts, `packed` and `extern` layout, function pointers, unions in memory; `@Vector`; inline asm with register operands (x86_64 only) |
| `floatops`, `floatconv`, `floats` | f16 to f128, bit-exact on x86_64-linux, IEEE-754 rounding ([docs/floats.md](docs/floats.md)) |
| `threads`, `atomics` | atomics and fork-join threads that take turns at sync ops, with a data-race check; the RC11 memory model (message passing, store buffering, 2+2W, a lock-free stack) ([docs/std-models.md](docs/std-models.md)) |
| `sync`, `iogroup` (0.16.0) | `Io.Mutex`, `Io.Condition`, `Io.Event`, `Io.Semaphore`, `Io.RwLock`, translated from their std code, on a futex model; `Io.Group` (a model: a task is a thread) |
| `threadsync` (0.15.2) | `Thread.Mutex`, `Thread.Condition`, `Thread.ResetEvent`, `Thread.WaitGroup`, translated from their std code |

Threaded examples have partial-correctness and safety proofs over all schedules in the model: completed runs return the stated result, and no schedule gives a data race, deadlock or another error. These proofs allow no result (including out-of-fuel runs); they do not prove termination or fairness. See the [proved examples and concurrency logic](docs/proofs.md#proved-examples).

## Start here: check a proof

Install [elan](https://github.com/leanprover/elan#installation), Lean's toolchain manager, then run these commands from the repository root:

```sh
lake build Proofs.Basic.Proofs
lake env lean tutorials/first-proof/Main.lean
```

Lake uses the Lean version pinned in `lean-toolchain`; the first build downloads it and builds the dependencies. A successful build followed by Lean exiting with no errors checks a theorem that an on-time job has zero tardiness. This uses the committed translation, so you can start **without Zig or a patched compiler**.

The [getting-started guide](docs/getting-started.md) walks through the Zig source, generated Lean, and a small proof exercise. It then shows how to translate your own file. air2lean generates definitions; you write the properties and proofs.

## How it works

The Zig compiler does semantic analysis (`Sema`) and produces **AIR** (Analyzed Intermediate Representation). In AIR, `comptime` is already evaluated, generics are monomorphized, every type is known, and each safety check is explicit. A small compiler patch writes AIR as JSON. air2lean reads that JSON and writes one Lean definition per function.

```
foo.zig ──patched zig──▶ *.json ──air2lean──▶ Gen.lean ──lean──▶ proofs checked
                                                  ▲
               compiled Zig ◀── differential tests ┘
```

| Part | Where |
|---|---|
| Compiler patch (AIR → JSON) | [`zig-patch/`](zig-patch/README.md), format in [`docs/air-json.md`](docs/air-json.md) |
| Translator | `Air2Lean/` (parser, per-version normalizer, subset checker, emitter) |
| Runtime semantics + lemmas | `ZigLean/` (floats: `ZigLean/Float/`, [docs/floats.md](docs/floats.md); separation logic: `ZigLean/Sep/`, [docs/proofs.md](docs/proofs.md)) |
| Generated code, proofs | `Proofs/<Ex>/`: `Gen.lean` (generated, [naming rules](docs/generated-code.md)) and the proofs |
| Differential tests | `tests/diff/`, `scripts/diff.sh` |

## Example

```zig
pub fn tardiness(end: u32, due: u32) u32 {
    return if (end > due) end - due else 0;
}
```

The generated Lean (`Proofs/Basic/Gen.lean`) has the type `BitVec 32 → BitVec 32 → Zig.Result (BitVec 32)`, where `Zig.Result` is `ExceptT Zig.Error Option`: `throw` is a safety panic, `none` is non-termination. A proof (`Proofs/Basic/Proofs.lean`):

```lean
theorem tardiness_spec (a b : BitVec 32) :
    tardiness a b = pure (if b.toNat < a.toNat then a - b else 0)
```

`end - due` is a checked subtraction in Zig. The proof shows it never panics.

## Translate your own Zig

Once you have a stock Zig 0.16.0 on `PATH` and elan, build the patched compiler:

```sh
scripts/doctor.sh
zig-patch/build.sh 0.16.0
```

Then build the translator, dump AIR, translate it, and check the generated Lean in one command:

```sh
scripts/translate.sh myfile.zig -o MyGen.lean --namespace My
```

The [single-file workflow](docs/getting-started.md#translate-your-own-file) includes a complete source file and a separate proof, with the module build needed to import generated code. The [compiler setup notes](zig-patch/README.md) explain supported hosts, bootstrap requirements, and the AIR-only compiler.

### Before a PR

For Linux checks on a Docker host, use the local Ubuntu 24.04 runner (Python 3.12,
pinned x86_64 Lean/Zig, matching CI's float/export target):

```sh
scripts/local-ci.sh targeted 0.16.0 "threads atomics" # focused pipeline + proofs
scripts/local-ci.sh full 0.16.0                      # one complete non-mutation CI row
scripts/local-ci.sh matrix                          # all three versions + five mutation shards
```

Run the focused checks while editing, then the matrix locally before using GitHub CI
as final verification. The 0.14.1 row uses CI's restricted examples and skips the
differential harness; 0.15.2 also builds the macOS threadsync translation's proofs.
Full and matrix modes execute the actual shell steps and environments from
`.github/workflows/ci.yml`, including coverage, budgets, project/flow gates and proof
receipts. Unsupported workflow syntax fails explicitly. Only checkout/cache/upload
actions and the three equivalent pinned tool setup recipes are replaced locally.
Matrix rows and mutation shards run sequentially in one container limited to 8 GiB
memory (including swap), two CPUs and 512 processes. The container always uses
`linux/amd64`, preserving CI's x86 shell, coreutils, example selection and GNU
compiler target. On an arm64 Docker engine, only Ubuntu's Python 3.12 and its YAML
package use native arm64 binaries; Python memory gates then exclude x86 emulator
overhead. Lean, Zig and other tools remain x86 binaries. The first compiler build
can be slow. Docker Desktop provides the required binary emulation on Apple
Silicon; an arm64 Linux engine needs x86 binfmt support.

The runner snapshots current contents of Git-tracked files, including staged additions
and unstaged edits/deletions. Stage new source files first (`git add`); untracked files,
Git metadata and host `.lake`/compiler caches are excluded. Tests work on a private
writable checkout, so generated translations and mutation tests never change host files.
Zig and elan downloads use the checksums in `zig-patch/versions.toml`; Lean uses
`lean-toolchain`. Linux toolchains persist in `air2lean-local-linux-toolchains`
(override with `AIR2LEAN_LOCAL_TOOL_VOLUME`); Lake outputs persist in separate
`air2lean-linux-amd64-*` volumes, namespaced by the toolchain volume name so
different toolchain volumes also have separate Lake caches. Concurrent runs sharing these
caches are rejected. GNU `timeout` (or macOS `gtimeout` from coreutils) bounds each attached
run to six hours; override with `AIR2LEAN_LOCAL_TIMEOUT`. Without it, stop the runner
with Ctrl-C. Cleanup removes only its own container and temporary source snapshot.

The equivalent native commands are:

```sh
scripts/check.sh       # goldens, translate, build, differential test
lake build Proofs      # check the proofs
scripts/review.sh      # focused parser, runtime, proof, emission/exporter and input regressions
scripts/no-sorry.sh    # no sorry/admit/native_decide
scripts/mutate.sh      # a changed function must fail a test
```

`scripts/review.sh` needs the complete review suite from the integration stack. It does not build a patched compiler. To additionally check exported JSON with an existing patched compiler, set `AIR2LEAN_REVIEW_ZIG14`, `AIR2LEAN_REVIEW_ZIG15` or `AIR2LEAN_REVIEW_ZIG16` to its absolute path and `AIR2LEAN_REVIEW_TRANSLATOR` to the built translator; CI does this for its selected Zig version. The [review strategy](REVIEW_STRATEGY.md) and [baseline coverage ledger](REVIEW_COVERAGE.tsv) describe the review scope; the CI workflow runs the integration checks for its selected Zig version.

The float model follows x86_64-linux. On another host (for example an arm64 Mac) the diff test counts the float results that differ by target as `host=N`, not as mismatches: `tests/diff/<ex>/host.txt` lists those functions. CI (x86_64-linux) checks them.

## Scope

The supported subset includes checked, wrapping and saturating arithmetic; control flow and recursion; structs, enums, unions, optionals and error unions; pointers, slices and byte-level memory; heap allocation; floats and vectors; selected atomics, threads and std synchronization primitives. Inline asm is modeled as opaque functions with register operands on x86_64. See the [subset reference](PLAN.md#subset), [generated-code guide](docs/generated-code.md), and [std models](docs/std-models.md) for restrictions.

Unsupported features include `threadlocal` and `extern` globals, std functions without a translation or model, detached threads and the excluded async/thread operations listed in the references. Translation rejects AIR outside the checked subset; it does not establish properties of arbitrary Zig programs.

| In | Out |
|---|---|
| integers of any width, `bool`, floats (`f16`…`f128`) | |
| checked, wrapping (`+%`), saturating (`+\|`) arithmetic | `threadlocal` and `extern` globals |
| `if`, `switch`, `while`, `for` | a std function that is not translated and has no model ([docs/std-models.md](docs/std-models.md)) |
| local `var`, also one whose address escapes; `@ptrCast`, `packed` and `extern` layout | |
| enums (also non-exhaustive), tagged, bare, `extern` and `packed` unions | |
| slices `[]T`, many-pointers `[*]T`, sentinel pointers, arrays (also `[N:s]T`) | |
| atomics on an integer, enum, `bool` or packed struct pointee, fork-join threads that take turns at sync ops, with a data-race check; futex waits and wakes; std sync primitives translated from their std code (`Io.*` 0.16.0, `Thread.*` 0.15.2); `Io.Group` (a model); yield and audited spin hints with no fairness guarantee ([model](docs/progress-hints.md)) | `Thread.detach`, `Io.futexWaitTimeout`, `Io.async`/`Future` |
| structs and unions passed and returned by value | |
| calls, recursion, mutual recursion, optionals (`?T`), error unions (`E!T`); unions and error unions in memory | |
| `@Vector(N, T)` over integers, floats and `bool`: `splat`, `select`, `shuffle`, `reduce`, and every lane-wise op (arithmetic, division, `@min`/`@max`, `@addWithOverflow`, bitwise, shifts, comparisons, casts, float ops) | a pointer to an individual `bool` vector lane; integer or float vectors in memory whose lanes have a non-byte width or scalar ABI padding (`u9`, `u24`, `u40`, `f80`, for example) |
| single pointers `*T`, `?*T`, pointer aliasing (byte-level memory) | |
| scalar nonoptional C/allowzero pointer null tests, casts and direct access ([fragment](docs/null-pointers.md)) | nullable-pointer storage/aggregates/optionals, volatile/null-bit/slice representations and nullable projections |
| `@memset`, `@memcpy`, `@memmove`; globals, string literals, `@tagName`, `@errorName` | |
| `std.mem.Allocator` (a model with allocation failure), heap memory, std code such as `ArrayListUnmanaged` | |
| inline asm, register operands only, as opaque functions (x86_64 only) | |

Overflow, out-of-bounds access and `unreachable` become `throw`, not undefined behaviour. So does an access to memory that `ReleaseSafe` does not check (a dead block, out of bounds, misaligned): `throw .illegal`. Under the stated target and model assumptions, a proof that a function never throws in this model also shows that its `ReleaseFast` build has no illegal behaviour on those inputs. A Zig error (`error.Name`) is a return value, not a panic — it never goes through `Zig.Error`.

## What a proof covers

The Lean kernel checks the proof about the generated Lean code. Applying that result to compiled Zig also trusts Zig `Sema`, the AIR export patch, the translator, and the fidelity of the handwritten `ZigLean` semantics to the compiler and target. Memory uses a little-endian, 64-bit pointer ABI ([docs/generated-code.md](docs/generated-code.md#memory)); floats follow the stated reference target ([docs/floats.md](docs/floats.md)); allocator and concurrency results rely on the model assumptions in [docs/std-models.md](docs/std-models.md), including infallible thread creation and no load buffering. The differential tests check this correspondence on sampled inputs: `scripts/diff.sh` runs the compiled Zig and the generated Lean on the same inputs, including edge values, and compares results and panics.

## Zig versions

Supported: Zig **0.16.0** (default), **0.15.2** and **0.14.1** (Linux only; `basic`, `recursion`, `options`, `floatops`, `floats`, `errors`, `variants`, `pointers`, `layout`). `sync` and `iogroup` run on 0.16.0 only, `threadsync` on 0.15.2 only. One source serves every version: one exporter, one golden set, one translation and one set of proofs. A version adds only its differences (a `Compat` branch, a hook, the AIR, translation or float results that differ); the proofs hold for each version's translation. See [PLAN.md § Zig version support](PLAN.md#zig-version-support).

## License

Apache-2.0. See [LICENSE](LICENSE).
