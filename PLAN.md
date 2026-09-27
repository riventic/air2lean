# Plan

## Status

| # | Milestone | State |
|---|---|---|
| M0 | Toolchain: patched Zig 0.15.2, Lean 4.34.0 | done |
| M1 | AIR JSON export (`zig-patch/`) | done |
| M2 | Semantics library (`ZigLean/`), incl. `loop_spec` | done |
| M3 | Parser + per-version normalizer | done |
| M4 | Translator: straight-line code, branches, calls | done |
| M5 | Translator: locals, loops, slices, structs | done |
| M6 | Differential tests: 4 examples, 18 functions × 300 inputs, 0 mismatches | done |
| M7 | Case study proofs (`Proofs/Basic/`) | 8 of 8 functions, incl. the loops `sum` and `totalWeightedTardiness` |
| M8 | CI, panic kinds in the diff test, `mutate.sh`, `no-sorry.sh` | done |
| M9 | Recursion: call groups → `mutual` + `partial_fixpoint` | done |
| M10 | Optionals and error unions (`?T`, `E!T`, `try`, `catch`, `orelse`, `.?`); JSON schema 2 | done |
| M11 | Zig 0.14.1: export patch, translator, CI job | done (Linux only) |
| M12 | Proofs for `recursion`, `options`, `errors` | done: 19 theorems over 18 functions, incl. mutual recursion, early-exit loops, `try` in a loop |
| M13 | Floats `f16`…`f128`: exact model (`ZigLean/Float/`), schema-3 export, translator, diff test (44,400 inputs, 0 mismatches on x86_64-linux), `compiler-rt` opt-in, proofs for `floats`/`floatconv` incl. rounding round trip and monotonicity | done |
| M14 | Zig 0.16.0 (default): one shared exporter (`Compat`), shared goldens and translation (`Canon.lean`), per-version float semantics (f128 `sqrt`, f128 `/` in `compiler-rt` mode), CI job | done |
| M15 | Enums (exhaustive and non-exhaustive) and tagged unions; places (a result built in `ret_ptr`, stores through field pointers of a local); JSON schema 4; `variants` example with proofs | done |
| M16a | Byte-level memory (`ZigLean/Mem/`: blocks, `Zig.Enc`, `Error.illegal`); single pointers `*T`, `?*T`; escaping locals as stack blocks; pure/memory function split; JSON schema 5 (sizes, alignments, field offsets); diff test with input buffers; `pointers` example with proofs (`swap` incl. `swap(p, p)`) | done |

Mutation check (`scripts/mutate.sh`): a `*` changed to `*%` in `scale` gives 279 mismatches; `Zig.add` throwing `.panic` in place of `.overflow` gives 166 mismatches; `orelse xs.len` changed to `orelse 0` in `findOr` gives 144 mismatches; ties-to-even changed to ties-away in the float rounding gives 77 mismatches; a generated `Light.ofInt?` that accepts the unnamed value 3 gives 1 mismatch; a `Zig.store` that writes one byte too few gives 802 mismatches. So the tester sees a changed result, a changed panic kind, a changed rounding rule, a changed enum conversion and a changed memory write.

## Next

v1: the rest of the language, one milestone per PR.

| # | Milestone |
|---|---|
| M16b | Mutable slices, `@memcpy`/`@memset`, globals, string literals, bare/`extern` unions |
| M17 | Separation logic (`ZigLean/Sep/`), pointer proofs |
| M18 | Allocators: a model of the `mem.Allocator` API with an allocation-failure oracle; `ArrayListUnmanaged` translated from std |
| M19 | SIMD `@Vector` |
| M20 | `@ptrCast`, `packed`/`extern` layout, function pointers |
| M21 | Inline asm with register operands only, as opaque functions |
| M22 | Atomics, fork-join threads with a data-race check |
| M23 | Upstream the AIR export; v1.0.0 |

## Decisions

| Topic | Decision | Reason |
|---|---|---|
| AIR source | A compiler patch writes one JSON file per function (`ZIG_AIR_JSON_DIR`). | A release build prints no AIR: `--verbose-air` on stock 0.15.2 exits 0 with no output. The text dump has no stable grammar. |
| JSON types | Type table: each type is written once, and uses refer to it by ID. | Inline types repeat deeply nested std types. One file grew too big to parse, and a run took 2.5 min. |
| Function filter | `ZIG_AIR_JSON_FILTER=<prefix>` | Skip std functions. |
| Build mode | `-OReleaseSafe -fno-error-tracing` | Safety checks stay explicit in AIR. `Debug` adds error-return-trace code to every function. |
| Translator language | Lean 4, no dependencies | One toolchain. Fast builds. |
| Integers | `BitVec n` + a signedness flag per operation | `bv_decide` and `BitVec` lemmas do the bit-level work. |
| Effects | `Zig.M σ α := StateT σ (ExceptT Error Option) α` | `throw` = safety panic. `none` = does not terminate. Lean core has `partial_fixpoint` support for this stack. |
| Locals | One generated `Locals` structure per function, held in the state. `load`/`store` = `get`/`modify`. | No SSA pass. It is sound because an `alloc` whose address escapes is a stack block in memory, not a `Locals` field (`Air2Lean/Memory.lean`). |
| Memory | Byte-level blocks (CompCert style); a pointer is a block and an offset; a function that uses memory returns `Zig.MemM α` (`docs/generated-code.md` §Memory) | Pointer bytes keep their block, so a stored pointer stays exact. A pure function keeps `Zig.Result`, so every v0 proof stays unchanged. |
| Control flow | One generated `Exit` type per function (`ret`, `br_k`, `rep_k`). A block is a `match` on the exit, and a loop is `Zig.loop`. | This maps AIR's structured `block`/`br`/`loop`/`repeat` directly. |
| Panics | A call to a `noreturn` function, `unreach` or `trap` becomes `throw`. | This is how Sema lowers safety checks. |
| Loop bodies | Each loop body is a named definition `f.loop<k>` that takes the values it reads as parameters. The repeat test is a named `f.again<k>`. | A proof can then name both and apply `Zig.loop_spec`. |
| Host compiler | `build.sh` requires a host `zig` of exactly the target version. | The Zig compiler source normally builds with the same release. Bootstrapping from source (`bootstrap.c`, CMake + LLVM) is out of scope. |

## Zig version support

Supported: **0.16.0** (default), **0.15.2** and **0.14.1** (matrix below). The design supports every major Zig release (each `0.x` minor, later `1.x`). The rule: one source for all versions; a version adds only its differences, each in one named place.

| Layer | Shared | Per version |
|---|---|---|
| Exporter | `zig-patch/air-json/json.zig` | its branch in `json.zig`'s `Compat`; `zig-patch/<version>/hook.patch` (the one-line call); URL + sha256 in `zig-patch/versions.toml` |
| JSON format | `docs/air-json.md`. Each file has `schema` and `zig_version`. AIR tags are written verbatim. | — |
| Canonical form | `Air2Lean/Air/Canon.lean`: rewrites the AIR patterns that differ between versions for the same code, and numbers instructions without debug instructions | — |
| Normalizer | `Air2Lean/Air/Normalize.lean`: one tag table → internal `Op` | a version case only for a subset tag that differs (none today) |
| Checker, emitter, `ZigLean` | work only on `Op` | the float ops whose result differs by version: `FCtx.zigVersion` in `Emit.lean` picks the def (`docs/floats.md` §Per-version differences) |
| AIR goldens | `tests/golden/<ex>/air/` | a file in `tests/golden/<version>/<ex>/air/` replaces the shared file of that name |
| Translation | `Proofs/<Ex>/Gen.lean` (the default version's) | `tests/golden/<version>/<ex>/Gen.lean` where it differs |
| Proofs | `Proofs/<Ex>/Proofs.lean`, built in every full CI job against that version's translation | — |
| Float probe | `tests/floatprobe/expected.txt` | `expected.<version>.txt`: only the lines that differ |
| CI | one job per version (`.github/workflows/ci.yml`) | — |

Support matrix:

| Zig | State |
|---|---|
| 0.16.0 | supported, default |
| 0.15.2 | supported |
| 0.14.1 | supported for `basic`, `recursion`, `options`, `floatops`, `floats`, `errors`, `variants` (`floatconv` differs: 0.14.1 lowers the `@intFromFloat` check differently, `zig-patch/0.14.1/TAGS.md`). Builds on Linux only: it cannot link on macOS 26. CI checks that its translation equals the committed one (or its `tests/golden/0.14.1/` override); the diff test runs in the 0.16.0 and 0.15.2 jobs. |

**To add a Zig version** (add only differences; never copy a shared file):
1. Add its source and host-zig URLs and sha256 to `zig-patch/versions.toml`.
2. Add `zig-patch/<version>/hook.patch` (the call after the function body is analysed in `src/Zcu/PerThread.zig`). Build with `zig-patch/build.sh <version>`; fix each compile error in a new `Compat` branch of `zig-patch/air-json/json.zig`.
3. Compare the AIR tag list in `src/Air.zig` with the previous version. Add the version to `supportedVersions` in `Normalize.lean`; add a tag case only if a subset tag differs.
4. `AIR2LEAN_ZIG_VERSION=<version> scripts/check.sh`. If the AIR of an example differs: if the same code gives a different AIR pattern, rewrite it in `Canon.lean` so that the translation stays shared; copy only the differing AIR files to `tests/golden/<version>/<ex>/air/`. Write each difference in `zig-patch/<version>/TAGS.md`.
5. Run `scripts/floatprobe.sh` with the version. Each changed float result is a model difference: a named def in `ZigLean/Float/`, picked in `Emit.lean` by `FCtx.zigVersion`, and a line in `tests/floatprobe/expected.<version>.txt`.
6. Add the version to the CI matrix and the table above.

## Subset

| In | Out |
|---|---|
| integers of any width, `bool`, floats (`f16`…`f128`) | |
| checked, wrapping, saturating arithmetic | mutable slices, many-pointers, globals, string literals (M16b) |
| `if`, `switch`, `while`, `for` | allocators, heap |
| local `var`, also one whose address escapes; a result built in `ret_ptr` | `@ptrCast`, packed layout |
| read-only slices `[]const T` in a pure function | inline asm, threads, atomics |
| structs by value | SIMD vectors, `async` |
| calls, recursion | arrays, unions and error unions in memory (M16b) |
| optionals `?T`, error unions `E!T`, `try`, `catch`, `orelse` | unions without a tag |
| enums (also non-exhaustive), tagged unions `union(enum)` | |
| single pointers `*T`, `?*T`, aliasing; loads and stores of ints, `bool`, floats, pointers, optionals, enums and structs | |

## Risks

| Risk | Mitigation |
|---|---|
| AIR changes each Zig release | Version-specific code only in the patch and the normalizer. Golden files show the exact change. |
| A safety check is lowered in a form the translator does not recognize, so the model is too optimistic | Differential tests on edge inputs (0, max, min, empty slice). |
| An escaping `alloc` makes the `Locals` model unsound | Any use of a place other than a `load`/`store`/field pointer makes the `alloc` a stack block (`Air2Lean/Memory.lean`). |
| The model's size rule for a type differs from the compiler's | `Check.lean` compares every type in memory with the exporter's `abi_size`/`abi_align` and rejects a difference. |
| Loop proofs are slow to write | Unfolding lemmas for `Zig.loop`. Prefer `for` over slices. |
