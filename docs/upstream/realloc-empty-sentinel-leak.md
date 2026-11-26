# Draft upstream bug: `Allocator.realloc` of an empty sentinel slice leaks the sentinel item (Zig 0.17.1)

Status: draft, not filed. Target: ziglang/zig (`lib/std/mem/Allocator.zig`, `reallocAdvanced`).
Zig 0.17 accepts `realloc`, `remap` and `resize` of a sentinel slice and counts the sentinel
item of the old slice (`mem.absorbSentinel`). `reallocAdvanced` still tests `old_mem.len == 0`
before it absorbs the sentinel, and takes it for "nothing allocated":

```zig
if (old_mem.len == 0) {
    return self.allocAdvancedWithRetAddr(T, .fromByteUnitsOptional(slice_info.attrs.@"align"), new_n, return_address);
}
```

An empty `[:s]T` that `allocSentinel(T, 0, s)` made is one item (the sentinel), so the new buffer
is allocated and the old item is never freed. `free`, `remap` and `resize` are not affected:
`free` absorbs first, and `remap` and `resize` return `null` and `false` for a length of 0.

## Reproducer

```zig
const std = @import("std");
test "realloc of an empty sentinel slice" {
    const a = std.testing.allocator;
    const s = try a.allocSentinel(u8, 0, 0);
    const g = try a.realloc(s, 4);
    a.free(g);
}
```

Observed with stock Zig 0.17.1 and 0.17.0 (`zig test`, aarch64-macos):

```
[SafeAllocator] (err): leaked [addr: ..., len: 1 (0x1) align: 1] allocated at:
leak.zig:4:34: ... in test.realloc of an empty sentinel slice (test)
    const s = try a.allocSentinel(u8, 0, 0);
1 tests leaked memory.
```

Expected: no leak. The test for "nothing allocated" is on the absorbed slice
(`mem.absorbSentinel(old_mem).len == 0`), as in `free`.

## In air2lean

No mitigation is needed: the translation is the std code, and the model shows the leak.
`Interfaces.GrowSpec.realloc8_empty` and `realloc32_empty`
(`tests/roadmap/interfaces/Interfaces/GrowSpec.lean`) state it for every allocator that meets
`CAllocSpec`: after `a.realloc(s, n)` of an empty `[:0]T` the caller holds the new buffer and
the old grant. The proofs of growth (`append*_grant`, `resize*_grant`) ask for a nonempty slice.

## Related: Zig 0.15.2 and 0.14.1 hand the allocator the slice without its sentinel

Before 0.16, `realloc`, `remap` and `resize` take the old memory as `mem.sliceAsBytes(old_mem)`,
which is `len * @sizeOf(T)` bytes for a `[:s]T`, while `allocSentinel` allocated and `free` gives
back `(len + 1) * @sizeOf(T)` bytes. An allocator is called with a memory length that is not the
allocation's. Zig 0.16.0 rejects the calls at compile time and 0.17 counts the sentinel, so this
is fixed upstream and needs no report.

Native witness: stock Zig 0.15.2 and 0.14.1, `zig test -target aarch64-linux-musl`, run in a
native `linux/arm64` container. The size-checking `std.testing.allocator` detects the mismatch:

```zig
test "realloc of a sentinel slice" {
    const a = std.testing.allocator;
    const s = try a.allocSentinel(u8, 7, 0);
    const g = try a.realloc(s, 4000);
    a.free(g);
}
```

```
[gpa] (err): Allocation size 8 bytes does not match free size 7. Allocation:
t.zig:4:34: ... in test.realloc of a sentinel slice (test)
 Free:
t.zig:5:28: ... in test.realloc of a sentinel slice (test)
```

(both versions; the test runner then crashes while it prints the trace). So the calls are a std
bug on those versions, and the translator-side consequence is that they have no proof from
`CAllocSpec`, whose `remap`, `resize` and `free` ask for the memory at the grant's length:
`tests/roadmap/interfaces/check.sh` pins that the 0.17.1 proofs stop at that precondition over
the 0.15.2 and 0.14.1 translations. A client on those versions reallocates the absorbed
`len + 1`-item buffer (`tests/roadmap/interfaces/wide.zig`), which is proved on every version.
