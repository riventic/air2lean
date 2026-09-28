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
| M16b | Slices `[]T`, many-pointers, sentinel pointers, arrays (`Vector`) in memory; `@memset`, `@memcpy`, `@memmove`; globals and string literals (`mem0`); `@tagName`, `@errorName`; `Zig.readSlice` for a pure callee; JSON schema 6 (pointer, slice and aggregate constants, globals table); `Canon.lean` item reads and always-true checks; `slices` example (20 functions, 6000 diff inputs) with proofs | done |
| M17 | Separation logic (`ZigLean/Sep/`): heaps, `∗`, `pts`, `arr`, `Triple` with the frame rule; rules for load, store, `@memmove`, `@memset`, `alloc`, `free`, loops (`loop_sep_spec`); `docs/proofs.md`; proofs `swap` (also `swap(p, p)`), `reverse` (a loop invariant), `copyWithin` (overlapping ranges), `fill`, the global counter. A tactic that reorders `∗` is not done: the proofs reorder heaps with `Heap.union_assoc` and `Heap.union_left_comm` | done |
| M18 | Allocator model (`ZigLean/Mem/Alloc.lean`: `create`, `destroy`, `alloc`, `alignedAlloc`, `free`, `dupe`, `remap`; allocation `failAt` fails; `remap` always fails); std code translated through `examples/<ex>/filter` (`ArrayListUnmanaged`); `docs/std-models.md`; `TestAllocator` in the diff test, with the live allocations after each call; JSON schema 7 (`ZIG_AIR_JSON_FILTER` list, `no_fields`); heap cells with the block kind; `loop_sep_ghost`; `lists` example (4 functions, 1200 diff inputs) with proofs `push`, `reverse` (a linked list), `freeAll` (no bytes owned after it). `append` has no proof: its `@memcpy` alias check needs an address fact (every block ends below `Mem.nextAddr`) that no assertion can state | done |
| M21 | Inline asm, register operands only, x86_64 (`docs/generated-code.md` §Inline asm): one `opaque` per distinct (source, ordered constraints, operand widths) (`Air2Lean/Emit.lean`'s `collectAsmOps`/`asmDefName`) — a proof gets only what it states about an op, no built-in axiom; JSON schema 8 (`assembly` instruction: source, volatile, clobbers, per-operand constraint/name/ref; `docs/air-json.md`); `Check.lean` rejects a memory or immediate constraint (an input may carry a matching constraint tying it to the sole output register, still a register operand). Diff test against a real archive implementation (`tests/diff/asm/asm.zig`), wired in with `@[csimp]` since the opaque has no defining equation and already lives in an imported module (`@[implemented_by]`/`@[extern]` cannot attach there); mutation (i) mutates the archive itself, the only diff-test mutation with no Lean-side equation to change. `asm` example (`bswap32`, `popcnt64`, `lzcnt64`) with proofs. Not in the 0.14.1 CI job: 0.14.1 has no inline-asm export support | done |
| M19 | SIMD `@Vector(N, T)` over integers and floats (`Zig.Vec`, `ZigLean/Vec.lean`): `splat`, `select`, `shuffle` (comptime mask, a `Zig.Vec` literal), `reduce` (`.Add`/`.Mul`/`.And`/`.Or`/`.Xor`/`.Min`/`.Max`, `Zig.Vec.reduce`/`reduceM`), lane-wise `add`/`sub`/`mul` (checked/wrapping/saturating, `Zig.Vec.map2`/`map2M`); JSON schema 9 (`vecLayout`); `vectors` example (17 functions: one or more per op above, a two-vector shuffle, `bool`-mask `@select`, float `.Min`/`.Max` reduce, a vector in memory; 5100 diff inputs, 0 mismatches) with proofs: `uDotWrap`'s full scalar spec (the explicit 4-term wrapping sum), `maxLane`'s domination property, `satAdd`'s per-lane spec, `reverse`'s exact shuffle, `fDot`'s scaffolding reduction only (float addition is not associative, so no scalar-sum claim), `interleave`'s exact two-vector shuffle, `pick`'s and `splatAdd`'s per-lane specs, `xorLanes`'s fold. `checkedAdd` has no proof: its `Vec.map2M` short-circuit needs `Vector.mapM`'s internal recursion | done |
| M22 | Atomics (`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`; JSON schema 10: `order`, `op`, `success_order`, `failure_order`) restricted to integer pointees; fork-join threads (`ZigLean/Mem/Thread.lean`: `Zig.Thread.spawn`/`join`, eager run, vector clocks, per-access footprint, race check giving `.illegal` for a non-atomic write race or `.nondet` for a non-commuting atomic race; `docs/std-models.md` §Thread model, `docs/generated-code.md` §Atomics and threads); rejects `Thread.detach`/`.yield`/`.spinLoopHint`/`Futex.*`/`Mutex.*`/`Condition.*` with a reason; `threads` example (`bump`, `parallelCounter`) with pinned `nondet`/`unspecified` counts for two racing functions (`tests/diff/threads/`); two new `mutate.sh` mutations, (k) and (l) (let `Xchg` commute; disable the race check). Proof: `Proofs/Threads/Proofs.lean`'s `bump_step` — one atomic-RMW step is race-free and keeps the counter invariant, sorry-free. The induction over `bump.loop4`'s variable iteration count and the 4-thread `spawn`/`join` composition needed for the full "counter = 4·n" theorem are not done: no proof in this repo reasons about a variable-bound loop over `Zig.MM` locals, and that induction is a bigger proof-engineering task than the rest of this milestone. The model itself is unaffected — it is checked by the diff test against real compiled/executed threaded Zig code, like every other example | done (proof scope cut, above) |
| M20 | Casts, layout and function pointers (`docs/generated-code.md` §Casts, layout and function pointers): `@intFromPtr`, `@ptrFromInt` (`castToNull`, `incorrectAlignment`), `@ptrCast`, `@constCast`, `@volatileCast`, `@alignCast`, `@fieldParentPtr`; packed structs (`Zig.Packed`, `ZigLean/Packed.lean`) with `@bitCast` to the backing integer and bit-pointers (`Zig.loadBits`/`storeBits`); `extern` structs; tagged unions in memory (`Check.lean`'s `unionLayout`); error unions in memory (`Zig.Enc (Except Zig.ErrName α)`, error codes as `Byte.errFrag`); function pointers (a 1-byte block per address-taken function, an indirect call dispatches on it); JSON schema 11 (`field_parent_ptr`, error-union pointer tags, a bit-pointer's `bit_offset`). bare unions (the exporter's `safety_tag`: a tagged union); `extern` and `packed` unions as bytes (`ZigLean/Union.lean`); `const` globals read-only (`Zig.BlockKind.constGlobal`: a write throws `.illegal`). `layout` example with proofs (packed round trip, `setMode`, `headerLen`, indirect calls; `Proofs/Layout/Mem.lean`: `Num` round trip, `setNum`, `numInt`, error-union `bump`, `writeTable` throws `.illegal`; in `ZigLean/Mem/Lemmas.lean` the error-union round trip and the `extern` union field read) and mutations (m), (n) | done |

Mutation check (`scripts/mutate.sh`): a `*` changed to `*%` in `scale` gives 279 mismatches; `Zig.add` throwing `.panic` in place of `.overflow` gives 166 mismatches; `orelse xs.len` changed to `orelse 0` in `findOr` gives 144 mismatches; ties-to-even changed to ties-away in the float rounding gives 77 mismatches; a generated `Light.ofInt?` that accepts the unnamed value 3 gives 1 mismatch; a `Zig.store` that writes one byte too few gives 1101 mismatches; a `Zig.memmove` that writes one byte too few gives 188 mismatches; an allocation that never fails at `Mem.failAt` gives 311 mismatches; a `Zig.Vec.reduce` that drops the last lane gives 371 mismatches; a generated `Flags.ofBits` that swaps two packed fields gives 787 mismatches. A `Mem.accessW` that does not check for a `const` global changes the pinned `.illegal` count of `writeTable` from 3 to 0. So the tester sees a changed result, a changed panic kind, a changed rounding rule, a changed enum conversion, a changed memory write, a changed allocation failure, a changed reduction, a changed packed layout and a missing read-only check.

## Next

v1: the rest of the language, one milestone per PR.

| # | Milestone |
|---|---|
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
| AIR goldens | `tests/golden/<ex>/air/` | a file in `tests/golden/<version>/<ex>/air/` replaces the shared file of that name; a file in `tests/golden/<version>/<ex>/air-<os>/` replaces it on that host OS only (`std.Thread` is OS-specific std code) |
| Translation | `Proofs/<Ex>/Gen.lean` (the default version's) | `tests/golden/<version>/<ex>/Gen.lean` where it differs |
| Proofs | `Proofs/<Ex>/Proofs.lean`, built in every full CI job against that version's translation | — |
| Float probe | `tests/floatprobe/expected.txt` | `expected.<version>.txt`: only the lines that differ |
| CI | one job per version (`.github/workflows/ci.yml`) | — |

Support matrix:

| Zig | State |
|---|---|
| 0.16.0 | supported, default |
| 0.15.2 | supported |
| 0.14.1 | supported for `basic`, `recursion`, `options`, `floatops`, `floats`, `errors`, `variants`, `pointers`, `layout` (`floatconv` differs: 0.14.1 lowers the `@intFromFloat` check differently, `zig-patch/0.14.1/TAGS.md`; `slices` uses `@memmove`, which 0.14.1 does not have). Builds on Linux only: it cannot link on macOS 26. CI checks that its translation equals the committed one (or its `tests/golden/0.14.1/` override); the diff test runs in the 0.16.0 and 0.15.2 jobs. |

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
| checked, wrapping, saturating arithmetic | |
| `if`, `switch`, `while`, `for` | allocators, heap |
| local `var`, also one whose address escapes; a result built in `ret_ptr` | |
| read-only slices `[]const T` in a pure function; atomics on an integer pointee (`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`); fork-join threads (`Thread.spawn`/`.join`) with a data-race check | |
| structs by value | `async` |
| calls, recursion; function pointers (an indirect call) | |
| `@Vector(N, T)` over integers and floats: `splat`, `select`, `shuffle`, `reduce`, lane-wise `add`/`sub`/`mul` | vector `div`, `@min`/`@max`, `@addWithOverflow`, bitwise/shift, negation; vector comparison (`cmp_vector`, rejected explicitly); a vector of another type |
| optionals `?T`, error unions `E!T`, `try`, `catch`, `orelse` | |
| enums (also non-exhaustive), tagged unions `union(enum)` | |
| single pointers `*T`, `?*T`, aliasing; loads and stores of ints, `bool`, floats, pointers, optionals, enums and structs | `threadlocal` and `extern` globals |
| slices `[]T`, many-pointers `[*]T`, sentinel pointers, arrays in memory; `@memset`, `@memcpy`, `@memmove` | an array with a sentinel as one value in memory |
| globals (`var`, `const`; a write to a `const` global throws `.illegal`), string literals, `@tagName`, `@errorName` | |
| `@intFromPtr`, `@ptrFromInt`, `@ptrCast`, `@constCast`, `@volatileCast`, `@alignCast`, `@fieldParentPtr`; `packed` structs (also bit-pointers) and `extern` structs; tagged, bare, `extern` and `packed` unions and error unions in memory | a packed struct field other than an integer, `bool` or packed struct; a `packed` union in a packed struct |

## Risks

| Risk | Mitigation |
|---|---|
| AIR changes each Zig release | Version-specific code only in the patch and the normalizer. Golden files show the exact change. |
| A safety check is lowered in a form the translator does not recognize, so the model is too optimistic | Differential tests on edge inputs (0, max, min, empty slice). |
| An escaping `alloc` makes the `Locals` model unsound | Any use of a place other than a `load`/`store`/field pointer makes the `alloc` a stack block (`Air2Lean/Memory.lean`). |
| The model's size rule for a type differs from the compiler's | `Check.lean` compares every type in memory with the exporter's `abi_size`/`abi_align` and rejects a difference. |
| Loop proofs are slow to write | Unfolding lemmas for `Zig.loop`. Prefer `for` over slices. |
