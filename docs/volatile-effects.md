# Volatile and device effects (L13)

The memory model (`ZigLean/Mem`) has ordinary, repeatable memory only: a read of an
unchanged block returns the same bytes, and nothing outside the program observes a
store. A `volatile` access is the opposite: each read or write is an observable effect
that may read or change device state, and it may not be merged, repeated, reordered
with other volatile accesses or removed. The translator therefore **rejects** every
volatile memory access. The only way to give one meaning is an explicit, project-declared
contract (below).

## Exporter audit

Volatility is a property of the pointer type in Zig AIR; `load`, `store`, the atomics,
`memcpy`/`memset` and the item/projection tags have no separate volatile flag. The shared
exporter (`zig-patch/air-json/json.zig`, used unchanged by 0.14.1, 0.15.2 and 0.16.0)
writes `volatile: bool` in every `ptr` type entry (`writeTypeEntry`, from
`ptrInfo().flags.is_volatile`). Every operand's type is in the file, so a volatile access
is distinguishable in exported AIR for all three versions; the exporter does not drop the flag.

| Evidence | Result |
| --- | --- |
| `ptr` type entries in committed AIR (goldens, roadmap exports; 474 files, schemas 11–12, all three versions) | 5507 entries, every one with an explicit boolean `volatile` |
| real export with `volatile: true` | `tests/golden/layout/air/layout.asVolatile.json` (0.16.0, `@volatileCast` to `*volatile u32`, no access): still accepted, translation unchanged |
| pointer constants (`resolvePtr`) | a volatile *leaf* is already exported `unsupported: "payload_volatile"`; a parent's volatile bit is address metadata |
| inline asm | `assembly` carries `volatile: bool` (schema 8) |
| `@prefetch` | the `prefetch` tag is exported only as the unsupported marker (`coverage/*.json`: `rejected-exporter-unsupported`) |

The decoder (`Json.parseLayout`) still reads a missing `volatile` as `false`, so that older
synthetic fixtures keep decoding. No real export lacks the field. A producer that omitted it
would bypass this check (see Residuals).

## Checker contract

`CheckCtx.checkVolatile` (`Air2Lean/Check.lean`) runs before every instruction check, in
both ordinary translation and `--diagnostics-json`. It rejects:

* a load, store, atomic load/store/RMW/`cmpxchg`, `ptr_elem_val`, `slice_elem_val`,
  `@memset`, either side of `@memcpy`, `ret_load`, a pointer-state test or set
  (`is_null_ptr`, `is_err_ptr`, payload-pointer `_set`, `unwrap_errunion_err_ptr`,
  `try_ptr`, `set_union_tag`) and an asm lvalue output, through a volatile pointer;
* a derivation that drops the qualifier (`@volatileCast` away, `@intFromPtr`, or a
  projection to a non-volatile pointer), so later accesses cannot look ordinary;
* a built-in std model call with an argument that contains a volatile pointer: no std
  model has a volatile contract.

Forming a volatile pointer, casting to one, comparing, storing, passing to translated
functions and returning one stays accepted. These are address metadata, not accesses. A callee
that accesses the pointer is checked itself.

Canonicalization runs first. `forwardReadOnlyCopies` already kept volatile slice-item reads in
place. It now also never forwards a local copy read through a volatile pointer, so
`var x = 5; (&x as *const volatile u32).*` stays a load and reaches the checker.
The item-read rewrites keep the volatile pointer operand, and the checker rejects the result.

Diagnostics use the stable code `VOLATILE_ACCESS`, phase `check`, category
`unsupported_semantics`, with a canonical instruction anchor and guidance. That
instruction's generic `INSTRUCTION_FAILURE` check is skipped. Ordinary translation fails with the
same message and leaves its output unchanged.

## Declared contract: model registry

A device access becomes translatable only via a project model registry binding
([external-models.md](external-models.md)). `ModelRegistry.check` requires:

* each direct volatile pointer parameter to be listed in `footprint.writes`. A device read
  can change device state, so a read-only footprint or a `preserves` binding is rejected.
  The binding is then `tracked`, and its `contract` states the observable effect;
* no nested volatile pointer in any parameter, so a model cannot receive a device
  capability that its footprint does not name.

Return values may contain volatile pointers: the caller's accesses are checked. As for
every binding, an `assumed` contract is reported as an assumption, not as evidence.

## Residuals

* **Generic volatile inline asm.** A register-only `asm volatile` is translated as a pure
  `opaque` function (M21, `docs/generated-code.md` §asm), so two calls with equal inputs
  are equal in Lean. That is the M21 opaque contract: a proof knows only what its caller
  states. Volatile asm with port I/O or counters (`in`, `rdtsc`) is therefore *modelled as
  repeatable*. It is not rejected, because the committed `asm.lzcnt64` golden is volatile.
  Exact `pause`/`isb` spin hints have their own C03 semantics.
* **Missing flag.** A producer that omits `volatile` is read as non-volatile. The patched
  exporter always writes it; a third-party producer must too.
* **Real-export qualification.** The synthetic fixtures follow the exporter schema. The fresh
  export of `tests/roadmap/volatile-effects/volatile_effects.zig` requires the patched compiler
  (commands below). It has not been run in this change.
* Volatile semantics (ordering among volatile accesses, environment-driven value changes,
  MMIO side effects) are not modelled. Rejection is the qualified behavior.

## Commands

```sh
lake build air2lean
python3 tests/roadmap/volatile-effects/test_cli.py --self-test
python3 tests/roadmap/volatile-effects/test_cli.py "$PWD/.lake/build/bin/air2lean"
# Real-export qualification (needs zig-patch/build.sh <version>; repeat per version):
air=$(mktemp -d)
ZIG_AIR_JSON_DIR="$air" ZIG_AIR_JSON_FILTER=volatile_effects. zig-air-0.16.0/bin/zig \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  tests/roadmap/volatile-effects/volatile_effects.zig
python3 tests/roadmap/volatile-effects/test_cli.py --export-dir "$air" "$PWD/.lake/build/bin/air2lean"
```
