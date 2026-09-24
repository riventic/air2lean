# Plan

## Status

| # | Milestone | State |
|---|---|---|
| M0 | Toolchain: patched Zig 0.15.2, Lean 4.34.0 | done |
| M1 | AIR JSON export (`zig-patch/`) | in progress |
| M2 | Semantics library (`ZigLean/`) | in progress |
| M3 | Parser + per-version normalizer | in progress |
| M4 | Translator: straight-line code, branches, calls | open |
| M5 | Translator: locals, loops, slices, structs | open |
| M6 | Differential tests | open |
| M7 | Case study proofs (`examples/basic`) | open |

Estimate for M1–M7: 1–2 days, with parallel agents.

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
| Locals | One generated `Locals` structure per function, held in the state. `load`/`store` = `get`/`modify`. | No SSA pass. It is sound because the checker rejects an `alloc` whose address escapes. |
| Control flow | One generated `Exit` type per function (`ret`, `br_k`, `rep_k`). A block is a `match` on the exit, and a loop is `Zig.loop`. | This maps AIR's structured `block`/`br`/`loop`/`repeat` directly. |
| Panics | A call to a `noreturn` function, `unreach` or `trap` becomes `throw`. | This is how Sema lowers safety checks. |

## Zig version support

v0 supports **0.15.2**. The design supports every major Zig release (each `0.x` minor, later `1.x`). AIR changes between releases, so the version-specific code stays at the two edges.

| Layer | Version-specific? | Where |
|---|---|---|
| Compiler patch | yes | `zig-patch/<version>/air-json.patch`; URL + sha256 in `zig-patch/versions.toml` |
| JSON format | no | `docs/air-json.md`. Each file has `schema` and `zig_version`. AIR tags are written verbatim. |
| Normalizer | yes | `Air2Lean/Air/Normalize.lean`: one tag table per Zig version → internal `Op` |
| Checker, emitter, `ZigLean` | no | They work only on `Op`. |
| Tests | yes | `tests/golden/<version>/`. The CI matrix runs one job per version. |

Support matrix:

| Zig | State |
|---|---|
| 0.15.2 | supported |
| 0.14.x | planned |
| 0.16.x | planned (when released) |

**To add a Zig version:**
1. Add its URL and sha256 to `zig-patch/versions.toml`.
2. Port the patch: `src/Air/json.zig` + the hook after `analyzeFnBodyInner` in `src/Zcu/PerThread.zig`. Check the AIR tag list in `src/Air.zig` for new, renamed and removed tags.
3. Add a normalizer table. Start from the nearest version and change only the tags that differ.
4. Build with `zig-patch/build.sh <version>`, then dump `examples/` into `tests/golden/<version>/`.
5. Run the differential tests and proofs against that version. Add it to the CI matrix and the table above.

## Subset (v0)

| In | Out |
|---|---|
| integers of any width, `bool` | floats |
| checked, wrapping, saturating arithmetic | mutable pointers, aliasing |
| `if`, `switch`, `while`, `for` | allocators, heap |
| local `var` whose address does not escape | `@ptrCast`, packed layout |
| read-only slices `[]const T` | inline asm, threads, atomics |
| structs by value | SIMD vectors, `async` |
| calls, recursion | optionals, error unions (later) |

## Risks

| Risk | Mitigation |
|---|---|
| AIR changes each Zig release | Version-specific code only in the patch and the normalizer. Golden files show the exact change. |
| A safety check is lowered in a form the translator does not recognize, so the model is too optimistic | Differential tests on edge inputs (0, max, min, empty slice). |
| An escaping `alloc` makes the `Locals` model unsound | Conservative escape check that rejects on any doubt. |
| Loop proofs are slow to write | Unfolding lemmas for `Zig.loop`. Prefer `for` over slices. |

## Later

- Optionals and error unions (`?T`, `E!T`).
- Immutable pointers `*const T`, then mutable pointers with a separation-logic memory model.
- Floats (IEEE-754 model or uninterpreted).
- Ports to 0.14.x and 0.16.x.
- Upstream the export as a compiler debug feature.
