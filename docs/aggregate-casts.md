# Aggregate representation casts and optional pointers (L07)

Up to Zig 0.16.0, `@bitCast` of an array, `extern` struct or `extern` union reinterprets the
value's **in-memory representation**, padding included. Zig 0.17.0 changed `@bitCast` to the
logical bit order and made `extern` struct and union casts compile errors. The rules below
apply to AIR with `zig_version` 0.14.1, 0.15.2 or 0.16.0 only (`ZigVersion.bitCast` is `.memory`,
`reprCastApplies` in `Air2Lean/Check.lean`). Any other version, and a checker context without a version, rejects
them.

## Representation casts

A `bitcast` whose two types differ and that has an array (no sentinel), `extern` struct or
`extern` union on either side translates to `Zig.reprCast T x` (`ZigLean/Mem/Repr.lean`). A
packed struct or union and another packed struct or union, a float or a `bool` of the same bit
size cast through their bits (`packedScalarCast`, `Zig.Packed.bitCast`) in every version:

1. Encode `x` with its `Zig.Enc` instance. Struct padding, the padding after a `uN` in its ABI
   slot (`u24` in 4 bytes), and the bits above a `uN` with `N % 8 ≠ 0` are undefined
   (`Byte.undef`, `Byte.part`).
2. Pad that image with undefined bytes to `T`'s size and decode `T` from it.

A destination part that needs an undefined bit throws `.unspecified`. Zig leaves those bits
open, and the model does not choose a value. A struct or array is a Lean value, so if any field
or item would hold an undefined bit, the whole cast throws. An `extern` union keeps its bytes,
so its undefined bytes throw only when a field read needs them.

The checker accepts the cast when both sides are an integer, float, `bool`, packed struct,
array, `extern` struct, `extern` union or vector, every part has a guaranteed in-memory layout,
and both sides have the same 0.16.0 `@bitSizeOf` (`reprBitSize`). For an array, the size is
`(len-1)·8·@sizeOf(E) + @bitSizeOf(E)`; for an `extern` type, the ABI size in bits; for a
vector, `len·@bitSizeOf(lane)`. A vector's memory image is its bit-packed lanes
(`Vec.packedEnc`, L09), as Zig 0.16.0's LLVM `bitCast` reinterprets it; `ZigLean/VecCast.lean`
proves vector → integer is `Vec.packBits`, integer → vector splits the lanes, and the round trip.
`[n]T` ↔ `@Vector(n, T)` is not a representation cast: lane `i` is item `i` for every item type
(0.16.0 copies a padded item such as `u24` lane by lane), so it is translated lane-wise
(`vectorLaneCast?`). An array and a vector of other item types are a representation cast only
when the source's items fill whole bytes (otherwise 0.16.0 copies item by item into lanes of
another type). A packed union is its bytes (its backing integer). It rejects casts that involve these parts at
any depth: an `auto` struct, a tuple or a tagged union (no guaranteed layout, which Sema also
rejects at the outer type in every version, `tests/roadmap/packed-casts/compile-errors`), a slice,
a sentinel array, error storage, or a pointer or optional pointer. One exception follows Sema:
Zig 0.14.1 and 0.15.2 check only the outer types, so an *array item* may be an `auto` struct or a
tagged union (`ZigVersion.bitCastAutoItems`); its memory image is the exporter's layout, padding
undefined and the tag included (`tests/roadmap/packed-casts/auto_items.zig`). An array of tuples
stays rejected: the memory model has no tuple layout. Pointer-bearing repr casts are rejected (fail
closed): the model's pointer bytes carry provenance and are not integer bits, so it could not
give Zig's address there. It also rejects casts whose bit sizes differ. Enums, pointers and
optionals on the outer side are rejected as before.

## Round trips: stated condition

`ZigLean/ReprCast.lean` (proof-only, not in the `ZigLean` umbrella):

- `reprCast_roundtrip`: if `Enc.encode y = Enc.encode x`, so that `x`'s bytes are exactly a
  `y` with no padding of either type and every byte defined, then `reprCast β x = pure y` and
  `reprCast α y = pure x`. This needs `LawfulEnc` of both types. The module provides
  `lawfulEnc_bitVec` (every width) and `lawfulEnc_vector` (arrays of lawful items).
  `reprCast_self` covers casting a value to its own type.
- `intOfBytes_undef`, `reprCast_int_undef`: an integer that needs an undefined byte throws
  `.unspecified`.
- Concrete cases: `[4]u8 ↔ u32` round-trips. `[2]u24 → u56` throws because it needs item 0's
  padding byte. `u56 → [2]u24` drops byte 3 into padding, so casting back throws.

No round trip is claimed without the condition.

## Optional pointers

`?*T` (single, non-C, non-allowzero pointee pointer) is `Option Zig.Ptr`, and null is `none`.
Its 8 bytes are zero (`optPtr_encode_null`). A wrapped pointer has the pointer's own bytes
(`optPtr_encode_wrap`).

| Zig | Model | Null rule |
|---|---|---|
| `*T` → `?*T` (`@ptrCast`, coercion) | `optPtrWrap p = some p` (Lean coercion), any version | never null (`optPtrWrap_ne_null`) |
| `@ptrCast(?*T)` → `*U` | `Zig.optPtrUnwrap` | null throws `.illegal` (`optPtrUnwrap_null`); safe builds check before the cast (ordinary AIR, `.panic` first) |
| `@intFromPtr(?*T)` | `Zig.optPtrAddr` | null is 0 (`optPtrAddr_null`) |
| `@ptrFromInt(n)` to `?*T` | `Zig.optPtrFromAddr` | 0 is null (`optPtrFromAddr_zero`); `n ≠ 0` is `optPtrWrap <$> ptrFromAddr n` |

`optPtrUnwrap_eq_pure`: unwrapping succeeds exactly on a wrapped pointer, so `?*T → *T → ?*T`
round-trips only for a non-null operand. A C/allowzero pointer converts to and from an
ordinary optional single/many pointer only through the explicit null mapping of
[null-pointers.md](null-pointers.md) (`Zig.ptrToOptional`/`Zig.ptrOfOptional`, checked before
these rules). Casts between optional pointers and slices or other integers, and between a
C/allowzero pointer and an optional slice, stay rejected.

## Evidence

`tests/roadmap/aggregate-casts/` (`check.sh`):

- `air/<version>`: exports of `aggregate_casts.zig` (the probe's casts) by patched 0.16.0, 0.15.2
  and 0.14.1 compilers (x86_64-linux, ReleaseSafe), pinned by `provenance.json`.
  `AggregateCasts/Gen.lean` is the 0.16.0 translation, compared byte for byte; the other two
  translate to the same text apart from the profile header. The compiler also emits the
  `@ptrFromInt` alignment check and the `?*T` unwrap null check, which the earlier hand-written
  AIR (`air-handwritten/`) omitted.
- `AggregateCasts/Proofs.lean`, checked by kernel evaluation and `rfl`:
  - round trips without padding (`[4]u8 ↔ u32`, `extern struct {u32, u32} ↔ u64`, and the
    generic theorem instantiated);
  - padding results that throw `.unspecified` (`Padded → [8]u8`, `[2]u24 → u56`, an `extern`
    union built from a narrower field);
  - padding bytes dropped (`[8]u8 → Padded`), and the failed round trips;
  - the `extern` union field reads;
  - the optional-pointer null rules for every memory state, the misaligned `@ptrFromInt` panic, and
    wrap/unwrap for a pointer with a nonzero address.
- `Model.lean`: compares the model's result bytes with `probe.zig`'s output from stock Zig 0.16.0
  on aarch64-macos (`aarch64-macos-ReleaseSafe.txt`; Debug and ReleaseFast print the same; no
  qualified claim for those modes, [build-modes.md](build-modes.md)).
  Every defined byte agrees. A model padding byte (`--`) matches any native byte, which was
  `00` in this run but is unspecified. The three casts the model leaves `.unspecified` are only
  recorded.
- `Checker.lean`: every accepted cast is accepted for 0.14.1, 0.15.2 and 0.16.0 and rejected
  for 0.17.0 or no version. It also checks the layout, bit-size and optional-pointer rejections.

The native probe covers only the listed values on one host. Packed unions, floats and float
arrays and vectors in casts, and arrays of `auto` structs and tagged unions (0.14.1, 0.15.2), are
exported for every version in `tests/roadmap/packed-casts`, with kernel-checked results and native
x86_64-linux outputs; casts of `auto` structs, tuples and tagged unions are compile errors there.
Sentinel arrays and error storage in casts have no export. Vector casts are
exported for 0.14.1-0.17.0 in `tests/roadmap/lang-long-tail` (`vector_casts.zig`, with
`std.mem.eql`'s `mem.eqlBytes`), with native probes of every version.
