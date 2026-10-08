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
* `Zig.Allocator.reallocSentinel` — that client composition — and `Zig.appendSentinel`.
* Raw vtable contracts `vtableAlloc`, `vtableResize`, `vtableRemap`, `vtableFree`. The raw calls
  are `inline` vtable dispatch and stay unrecognized by the translator.

## Proofs (`ZigLean/Sep/SentinelRealloc.lean`, `ZigLean/Sep/RawAlloc.lean`)

* `remapByteBuffer_owned`, `realloc_run`: under whole-block ownership every success path
  (in-place remap, moved remap, allocate/copy/free) owns exactly `remapBytes bs n`; the only
  failure is `OutOfMemory` with the caller heap unchanged. The frame is exact.
* `Triple.reallocSentinel`: for every policy, cap, failure trace and remap mode, success is a
  `sentinelBuf` of length `n` (whole `n + 1`-byte block, sentinel at `n`, sentinel byte counted
  in the request); failure is `OutOfMemory` and the original `sentinelBuf` (bytes and sentinel).
  `reallocSentinel_overflow` panics before any allocator decision. `sentinelReallocBytes_*`
  give size, sentinel, retained prefix (including the old sentinel byte on growth) and
  undefined growth.
* Client `Triple.appendSentinel`: one more byte, unchanged payload, `c` at the old length and
  the sentinel at the new length; failure keeps the original buffer. `sentinelBuf_of_newSentinel`
  and `Triple.freeSentinelBuf` connect it to `allocSentinel` and whole-block release.
* Raw: `rawAlignOk_iff` (`2 ^ k`, `k < 64`, hence `≤ 2 ^ 63`); `vtable*_illegal` and
  `rawBlock_illegal` (bad alignment, zero length, another allocation alignment, partial, inner,
  non-heap or empty memory); `Triple.vtableAlloc` (aligned fresh block or no change);
  `vtableFree_run`; `vtableResize_run` (in place at the same address or no change);
  `vtableRemap_run` (in place, moved to an aligned fresh block, or no change).

## Checks

Local results on aarch64-macos (this branch):

| Check | Result |
|---|---|
| `lake build ZigLean.Sep` (new modules, no `sorry`) | passed |
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
