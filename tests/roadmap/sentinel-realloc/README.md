# M04 sentinel reallocation and raw allocator contracts

## Scope

Zig 0.16.0 rejects `realloc` of a sentinel slice at compile time (`destination pointer
requires '0' sentinel`; `reallocAdvanced` returns `@TypeOf(old_mem)` from an unsentinelled
byte slice). A `[:s]u8` client therefore reallocates the absorbed `len + 1`-byte buffer and
stores the sentinel at the new length (`source.zig`). This change admits:

* `mem.Allocator.realloc` (E04 table row, Zig 0.16.0 only) for alignment-1 nonsentinel `[]u8`,
  emitted as `Zig.Allocator.realloc a s n`. It mirrors `reallocAdvanced`: empty `s` allocates,
  `n = 0` frees, otherwise the selected byte-remap policy is tried, then `n` bytes are
  allocated, the `min` prefix representation is copied and the old block is poisoned and freed.
  Other item types, alignments, sentinel-typed calls and other Zig versions are rejected.
* `Zig.Allocator.reallocSentinel`, that client composition, in the `std` model
  (`ZigLean/Mem/Alloc.lean`); `appendSentinel` is a test-local def (`Scenarios.lean`).
* The model's raw vtable interface `vtableAlloc`, `vtableResize`, `vtableRemap`, `vtableFree`
  with its preconditions (power-of-two alignment `2 ^ k`, `k < 64`, nonzero length, the whole
  live heap block of that alignment; a violation is `.illegal`). The raw calls are `inline`
  vtable dispatch and stay unrecognized by the translator.

## Proofs

The sentinel invariant is proved over the translated code, for every allocator:
`Interfaces.SentinelSpec` (`tests/roadmap/interfaces`) takes `source.zig` in the open
translation (`--allocator-model translated`, the allocator from the environment, EXT-05) and
walks `make`, `append`, `resize` and `release` and the generated `std.mem.Allocator` wrappers
with `fsym`, from `CAllocSpec` of the environment's allocator alone, on Zig 0.17.0, 0.16.0,
0.15.2 and 0.14.1: success is a buffer of the new length (`len + 1` bytes granted, the sentinel
byte counted) with the retained bytes and the sentinel at its end, `error.OutOfMemory` leaves the
old grant unchanged, and `release` returns the whole grant. The raw vtable contracts are the four
fields of `FAllocSpec`, proved for each translated allocator. The hand-written model's proof
layer (`ZigLean/Sep/{SentinelRealloc,RawAlloc}.lean`) is retired
([alloc-spec.md](../../../docs/alloc-spec.md#retired-claims)); `Check.lean` and the native
comparison below keep testing the `std` model that `--allocator-model std` still emits.

## Checks

Local results on aarch64-macos (this branch):

| Check | Result |
|---|---|
| `lake env lean --run tests/roadmap/sentinel-realloc/Check.lean` | 5 policy/failure grows, overflow, payload-only realloc, 12 raw-contract checks |
| `lake env lean --run tests/roadmap/sentinel-realloc/Pipeline.lean` | 1 emission, 6 rejections |
| model (`Scenarios.lean` + `Model.lean`) vs shipping Zig 0.16.0 `native.zig` ReleaseSafe | 9/9 identical rows |
| direct `realloc` of `[:0]u8` under shipping Zig 0.16.0 | compile error, as expected |
| origin/main vs branch translator on 95 retained AIR inputs | byte-identical |

`check.sh` is the ROOT/CI gate. It needs the patched Zig 0.16.0 exporter for the fresh source
export, and additionally compares the generated translation of `source.zig` with native:

```sh
AIR2LEAN_SENTINEL_ZIG_AIR=/abs/patched-0.16.0/zig \
AIR2LEAN_SENTINEL_ZIG_NATIVE=/abs/shipping-0.16.0/zig \
bash tests/roadmap/sentinel-realloc/check.sh
```

The fresh-export/generated-runtime part has not run yet. `TestAllocator` remap always fails,
so the native comparison covers the allocate/copy/free path; in-place and moved remap are
covered by `Check.lean` and the proofs. Sampled native agreement is correspondence evidence,
not a preservation theorem. No other target, Zig version or element type is qualified; general
(non-byte) realloc, `resize` recognition, allocator identity and address reuse remain out of scope.
