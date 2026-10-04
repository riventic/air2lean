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

For the threaded functions below, every completed run has the stated result, and no schedule gives a data race, a deadlock or another error. These are partial-correctness and safety proofs: they allow no result, including out-of-fuel runs, and do not prove termination or fairness. They use a rely–guarantee logic over the scheduler and a concurrent separation logic: each thread owns a part of the heap, and the parts move at a spawn, a join, a lock and an unlock ([docs/proofs.md](docs/proofs.md)).

| Function | Result | Std code under it | Proof |
|---|---|---|---|
| `threads.parallelCounter` | `4 * n` | — | `Proofs/Threads/Counter.lean` |
| `threads.disjoint` | `a + b` | — | `Proofs/Threads/Disjoint.lean` |
| `atomics.mpRelAcq`, `stackPush` | 0 or 42; 120 or 210 | — | `Proofs/Atomics/` |
| `sync.mutexCounter` | 4 | `Io.Mutex` | `Proofs/Sync/Mutex.lean` |
| `sync.handoff` | 7 | `Io.Mutex`, `Io.Condition`, `Io.Event` | `Proofs/Sync/Handoff.lean` |
| `sync.semaphoreCounter` | 4 | `Io.Semaphore` (with its `Io.Mutex`, `Io.Condition`) | `Proofs/Sync/SemCounter.lean` |
| `sync.rwLockRead` | 2, 12 or 22 | `Io.RwLock` (with its `Io.Mutex`, `Io.Semaphore`) | `Proofs/Sync/RwLock.lean` |
| `iogroup.groupCounter` | 3 | `Io.Group`, `Io.Mutex` | `Proofs/Iogroup/Counter.lean` |
| `threadsync.mutexCounter` | 4 | `Thread.Mutex` | `Proofs/Threadsync/Mutex.lean` |
| `threadsync.waitGroup` | 2 | `Thread.WaitGroup`, `Thread.ResetEvent`, `Thread.Mutex` | `Proofs/Threadsync/WaitGroup.lean` |
| `threadsync.handoff` | 7 | `Thread.Condition`, `Thread.ResetEvent`, `Thread.Mutex` | `Proofs/Threadsync/Handoff.lean` |

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

## Quick start

Needs: Zig 0.16.0 on `PATH` (to build the patched compiler), [elan](https://github.com/leanprover/elan).

```sh
zig-patch/build.sh 0.16.0          # patched compiler → ./zig-air-0.16.0/ (a few minutes)
lake build                         # runtime library + translator
scripts/check.sh                   # dump AIR, check goldens, translate, build, differential test
lake build Proofs                  # check the proofs
```

Translate your own file:

```sh
ZIG_AIR_JSON_DIR=out ZIG_AIR_JSON_FILTER=myfile. zig-air-0.16.0/bin/zig \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing myfile.zig
lake exe air2lean out -o MyGen.lean --namespace My --prefix myfile.
```

The Zig compiler only analyzes functions that something references. Use `export fn`, or reference each function in a `comptime { _ = &f; }` block.

### Before a PR

```sh
scripts/check.sh       # goldens, translate, build, differential test
lake build Proofs      # check the proofs
scripts/review.sh      # focused parser, runtime, proof, emission/exporter and input regressions
scripts/no-sorry.sh    # no sorry/admit/native_decide
scripts/mutate.sh      # a changed function must fail a test
```

`scripts/review.sh` needs the complete review suite from the integration stack. It does not build a patched compiler. To additionally check exported JSON with an existing patched compiler, set `AIR2LEAN_REVIEW_ZIG14`, `AIR2LEAN_REVIEW_ZIG15` or `AIR2LEAN_REVIEW_ZIG16` to its absolute path and `AIR2LEAN_REVIEW_TRANSLATOR` to the built translator; CI does this for its selected Zig version. The [review strategy](REVIEW_STRATEGY.md) and [baseline coverage ledger](REVIEW_COVERAGE.tsv) describe the review scope; local integration checks passed and Linux CI reruns are pending.

The float model follows x86_64-linux. On another host (for example an arm64 Mac) the diff test counts the float results that differ by target as `host=N`, not as mismatches: `tests/diff/<ex>/host.txt` lists those functions. CI (x86_64-linux) checks them.

## Scope

| In | Out |
|---|---|
| integers of any width, `bool`, floats (`f16`…`f128`) | |
| checked, wrapping (`+%`), saturating (`+\|`) arithmetic | `threadlocal` and `extern` globals |
| `if`, `switch`, `while`, `for` | a std function that is not translated and has no model ([docs/std-models.md](docs/std-models.md)) |
| local `var`, also one whose address escapes; `@ptrCast`, `packed` and `extern` layout | |
| enums (also non-exhaustive), tagged, bare, `extern` and `packed` unions | |
| slices `[]T`, many-pointers `[*]T`, sentinel pointers, arrays (also `[N:s]T`) | |
| atomics on an integer, enum, `bool` or packed struct pointee, fork-join threads that take turns at sync ops, with a data-race check; futex waits and wakes; std sync primitives translated from their std code (`Io.*` 0.16.0, `Thread.*` 0.15.2); `Io.Group` (a model) | `Thread.detach`, `Thread.yield`, `Thread.spinLoopHint`, `Io.futexWaitTimeout`, `Io.async`/`Future` |
| structs and unions passed and returned by value | |
| calls, recursion, mutual recursion, optionals (`?T`), error unions (`E!T`); unions and error unions in memory | |
| `@Vector(N, T)` over integers, floats and `bool`: `splat`, `select`, `shuffle`, `reduce`, and every lane-wise op (arithmetic, division, `@min`/`@max`, `@addWithOverflow`, bitwise, shifts, comparisons, casts, float ops) | a pointer to an individual `bool` vector lane; integer or float vectors in memory whose lanes have a non-byte width or scalar ABI padding (`u9`, `u24`, `u40`, `f80`, for example) |
| single pointers `*T`, `?*T`, pointer aliasing (byte-level memory) | |
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
