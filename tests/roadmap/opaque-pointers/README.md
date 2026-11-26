# Pointers to opaque types

An opaque type is `anyopaque` or a declared `opaque {}` (`const Handle = opaque {};`, with or
without declarations, also one a generic function returns). It has no size, no alignment and no
values, so the only thing a program has of it is a single-item pointer (`*Handle`,
`*const Handle`, `?*Handle`, `*align(N) Handle`). The translator has one type kind for both
(`Ty.opaque`, `Air2Lean/Air/Op.lean`): a declared opaque type gets exactly what `*anyopaque`
had, and nothing is specific to one name.

**The one boundary: the declaring module.** An opaque type that the standard library declares
(the entry's `module` is `std`: `Io.AnyFuture`, `c.pthread_t`) is not in the subset, in any
use. A pointer to one can be the handle of a hand-written std model (`Io.Future.any_future` is
the record of `Zig.Future`), whose bytes are the model's and not the native ones. The primitive
`anyopaque` and every opaque type declared outside std are admitted. Such a type may stand in
the type table (as the field of a modelled std type); only a use of it is rejected
([std models](../../../docs/std-models.md#opaque-std-handles)).

## What is in the subset

A pointer to an opaque type is a `Zig.Ptr` in the translation, an optional one an
`Option Zig.Ptr`, like every other single-item pointer.

| Use | Translation |
|---|---|
| copy, parameter, result, call through a function pointer, call of a bound `extern fn` (an `export fn` of the program) | the `Zig.Ptr` value |
| `a == b`, `h == null`, `h.?`, `h orelse d`, `?*T` wrap | pointer comparison (`Zig.ptrEqAddr`), `Option` operations |
| the pointer in memory: a variable, a struct or array or slice item, an optional field | `Zig.load`/`Zig.store` of the 8-byte pointer |
| `@ptrCast` of an error-free typed pointer to an opaque one (`*u32` → `*Handle`, `?*u32` → `?*Handle`) | the same pointer; every allocator model |
| a cast between opaque pointees (`*Handle` ↔ `*anyopaque`, `*Handle` → `*Other`) | the same pointer; every allocator model. Nothing is erased or recovered |
| a qualifier change (`*Handle` → `*const Handle`), `@alignCast` | the same pointer; the alignment check of `@alignCast` |
| `@intFromPtr(h)` | the address (`Zig.ptrAddr`) |
| `@ptrCast(@alignCast(h))` back to an error-free typed pointer (`*Handle` → `*u32`) | the same pointer after the alignment check, under `--allocator-model translated` only, as for `*anyopaque` ([allocator model](../../../docs/allocator-model.md)) |

A pointer to an opaque type has alignment 1 (`ptr_align` 1 in the export, as for `*anyopaque`).

## What is rejected

Zig rejects most of these at compile time. The translator does not rely on that: hand-made or
damaged AIR that has them is rejected too (`Checker.lean`, `negatives.py`).

| Use | Diagnostic |
|---|---|
| the opaque type by value (a parameter, result, variable, field, array item, optional payload) | `opaque type '…' has no size, alignment or values: only a single-item pointer to it is a value` |
| `[*]T`, `[]T`, `[*c]T` of an opaque `T` | the same |
| an opaque type of the standard library, also behind a single-item pointer (`?*Io.AnyFuture`, `f.any_future != null`) | `opaque type '…' is declared in the standard library: a pointer to it can be a handle of a hand-written std model, …` |
| a load or store through the pointer, of any type; an atomic load, store, rmw or cmpxchg; a field pointer | `a value in memory is outside the subset` (or the first row, for a load of the opaque type) |
| pointer arithmetic, an item pointer | `type … has no size in the AIR file` |
| an item access, `@memset`, `@memcpy` with it as destination or source | `item access through pointer type …, which has no items` |
| a global that holds a handle (`var g: ?*Handle = null`; Zig compiles it) | `global alias has unresolved or cyclic symbolic storage provenance`, as for `?*anyopaque` |
| an `extern var` of an opaque type (Zig compiles it) | `` `extern` global …: its type can hold a function pointer, a union or an unresolved type `` |
| a constant opaque pointer to a global (`const h: *Handle = @ptrCast(&global)`; Zig compiles it) | `global alias has unresolved or cyclic symbolic storage provenance`, as for `*anyopaque` |
| `@ptrFromInt` to an opaque pointer (Zig compiles it) | `recovering a symbolic error pointer from an integer or opaque value needs unsupported storage provenance`, as for `*anyopaque` |
| erasing a pointer to storage that can hold an error value (`*anyerror!u32` → `*Handle`; Zig compiles it) | `a pointer cast has unresolved or cyclic symbolic storage provenance` (an open error set) or a `symbolic error storage` diagnostic, as for `*anyopaque` |
| recovering a typed pointer in the default allocator model | `a pointer cast has unresolved or cyclic symbolic storage provenance`, as for `*anyopaque` |
| an entry of kind `opaque` named `anyopaque`, one without `module`, one with a size or with fields | a parse or schema error |

## Zig versions

The exporter is one source for all four versions (`zig-patch/air-json/json.zig`); the patched
compilers of 0.17.1, 0.16.0, 0.15.2 and 0.14.1 all write a declared opaque type as
`{"k": "opaque", "name": …, "module": …}` ([air-json](../../../docs/air-json.md#type)) and
`anyopaque` as before (`{"k": "other", "name": "anyopaque"}`: no committed export changes). An
export of an exporter that does not mark opaque types has `{"k": "other", "name": …}` for one,
the form of every unsupported type; it stays rejected with `type '…' is outside the subset
(otherwise unsupported)`, because nothing in it says that the type is opaque.

## Files

| File | Role |
|---|---|
| `opaque_ptrs.zig` | Source of the exported functions and the native `main` |
| `reject.zig` | Uses that Zig compiles and the translator rejects |
| `exports.json`, `exports.lock.json` | The exports (`scripts/fixture-exports.py`) and their pins |
| `air/<version>` | Compiler exports of the functions of the default allocator model (x86_64-linux ReleaseSafe) |
| `air-recover/<version>` | Compiler exports of the recovery of a typed pointer (`--allocator-model translated`) |
| `air-reject/<version>` | Compiler exports of `reject.zig` |
| `std_handles.zig`, `air-std/<version>` | Uses of std's `Io.AnyFuture` (0.17.1, 0.16.0), all rejected |
| `Runner.lean`, `RunnerRecover.lean` | The model's transcript of `main`, appended to the fresh translations |
| `expected.txt` | The transcript: the native lines, and `model` lines for the two `@alignCast` panics that would end the native run |
| `Checker.lean` | Checker controls on hand-built types and instructions: admitted types and casts in both allocator models, every rejection above |
| `negatives.py` | Changed type tables of the committed `copy` export, rejected through the CLI |

```sh
lake build ZigLean air2lean
tests/roadmap/opaque-pointers/check.sh                  # no compiler
tests/roadmap/opaque-pointers/check.sh --export         # the patched compilers reproduce the exports
tests/roadmap/opaque-pointers/check.sh --native <zig>   # a stock Zig's run prints the transcript
```
