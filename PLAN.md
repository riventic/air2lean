# Plan

Estimate: **5–7 months, one person**. Each milestone ends with a tagged release and green CI.

## Decisions

| Topic | Decision | Reason |
|---|---|---|
| Zig version | Pin **0.15.2**. Upgrade on purpose, one release at a time. | AIR is internal and changes each release. |
| AIR source | Small patch on the 0.15.2 tag that adds `--emit-air-json <path>`. | A release build prints no AIR: `zig build-obj --verbose-air` on Homebrew 0.15.2 exits 0 with no output (checked 2026-09-23). The text dump also has no stable grammar. |
| Translator language | Lean 4 | One toolchain. `Lean.Json` parses the input; the translator can be tested in the same repo as the proofs. |
| Integers | `BitVec n`, wrapped as `UInt'` types (`U8`, `U32`, `I64`, …) | `bv_decide` (SAT-backed) proves many bit-level goals automatically. |
| Effects | `Result α := ok α \| fail Error \| div` | Same shape as Aeneas. `fail` covers overflow, bounds, `unreachable`, `@panic`. `div` allows loops before a termination proof exists. |
| Loops | Translate to a fixpoint combinator in `Result`. Termination is a separate theorem. | Translation stays total and mechanical. Partial correctness first, total correctness when needed. |
| Build mode | Translate `Debug`/`ReleaseSafe` AIR. | Safety checks are explicit in AIR there. They map to `fail`. |

## Architecture

```
zig-patch/          patch + build script for zig 0.15.2 with --emit-air-json
Air2Lean/
  Air/Json.lean     AIR JSON schema → Lean data types
  Air/Check.lean    subset checker: reject unsupported instructions with a source location
  Promote.lean      local `alloc`/`load`/`store` → SSA values (escape check)
  Emit.lean         AIR → Lean source
ZigLean/            runtime semantics library (what generated code imports)
  Result.lean  Int.lean  Slice.lean  Struct.lean  Loop.lean
tests/
  golden/           .zig → expected .lean
  diff/             differential tests: Zig binary vs `#eval`
examples/           case studies with proofs
```

## Milestones

| # | Name | Weeks | Done when |
|---|---|---|---|
| M0 | Setup | 1–2 | CI builds patched Zig 0.15.2 (cached), Lean toolchain pinned via `lean-toolchain`, empty pipeline runs. |
| M1 | AIR export | 3–4 | `--emit-air-json` writes every function in the subset. Golden JSON tests for 20+ small functions. |
| M2 | Semantics library | 3–4 | `ZigLean` has checked / wrapping / saturating ops for all widths, casts (`@intCast`, `@truncate`), comparisons, `bool`. Each op has a lemma set tied to `BitVec`. |
| M3 | Straight-line code | 4–6 | Translate blocks, `cond_br`, `switch_br`, calls, safety-check branches → `fail`. Subset checker rejects the rest with a clear message. |
| M4 | Locals + loops | 3–4 | `var` locals promoted to SSA when the address does not escape. `loop`/`repeat`/`br` → fixpoint combinator. |
| M5 | Slices + structs | 3–4 | `[]const T` as `Array T` with bounds-checked index; `.len`; `for` over slices. Structs as Lean `structure`, field access, by-value copy. |
| M6 | Differential tests | 2–3 | Random-input harness: build Zig to a shared lib, call it and `#eval` the Lean definition, compare `ok`/`fail` and values. Runs in CI. |
| M7 | Case study | 2–4 | One realistic scoring function with proofs: no overflow in a stated input range, monotonicity in one argument, result equals a clean spec function. Write-up in `examples/`. |

## Risks

| Risk | Effect | Mitigation |
|---|---|---|
| AIR changes between Zig releases | Patch and translator break on upgrade. | Pin one version. Keep the patch small. Golden tests show exactly what changed. |
| Patch is rejected upstream / never upstreamed | Carry the patch for each version. | Keep it one file plus flag wiring. Offer it upstream as a debug feature. |
| Safety checks lowered in ways that are hard to recognize | Missed `fail` cases ⇒ model too optimistic. | Differential tests on inputs near limits (max int, empty slice, len-1). |
| Stack locals with escaping addresses | Promotion unsound. | Conservative escape check; reject on any doubt. |
| Proofs about loops are slow to write | Case study stalls. | Loop invariant helpers in `ZigLean/Loop.lean`; prefer `for` over slices, which maps to `List.foldl`-style lemmas. |

## Later (not v0)

- Optionals and error unions (`?T`, `E!T`).
- Floats, as an IEEE-754 model or as an uninterpreted type.
- Immutable pointers `*const T` that do not alias writes.
- Mutable pointers via a separation-logic memory model.
- Upgrade path to Zig 0.16+.

## Open questions

1. Termination: keep `div` in `Result`, or require a `decreasing_by` measure at translation time?
2. Should `@panic` messages be kept in `Error` for diagnostics?
3. Upstream route for the AIR JSON export: debug flag, or a compiler plugin once Zig has one?
