# Draft upstream bug: `@bitCast` of a sentinel-terminated array has three meanings (Zig 0.17.1)

Status: draft, not filed. Target: ziglang/zig (Sema `bitCast` and `Type.bitSize` of an array with a
sentinel, LLVM lowering of `bit_cast`, self-hosted x86_64 lowering). Zig 0.17 defines `@bitCast` on
the logical bit representation; `Type.bitSize` of `[n:s]T` is
`arrayLenIncludingSentinel * @bitSizeOf(T)` (`src/Type.zig`), so Sema accepts
`[3:7]u8` ↔ `u32`. What the sentinel's 8 bits are then depends on who evaluates the cast.
The translator's mitigation (`Air2Lean/BitCast.lean`, `sentinelBitCastFailure`): a Zig 0.17
`@bitCast` with a sentinel-terminated array on either side, also as an array or vector element, is
rejected by name (`tests/roadmap/packed-casts/reject_sentinel.zig`). Up to 0.16.0 the cast
reinterprets memory in every backend and mode, with the sentinel as one more item, and is
modelled (`tests/roadmap/packed-casts/sentinel_arrays.zig`).

## Reproducer

```zig
const std = @import("std");
noinline fn fromSent(a: u8) u32 {
    var x: [3:7]u8 = .{ 1, 2, 3 };
    x[0] = a;
    return @bitCast(x);
}
noinline fn toSent(a: u32, i: usize) u8 {
    const x: [3:7]u8 = @bitCast(a);
    return x[i];
}
noinline fn roundTrip(a: u32) u32 {
    const x: [3:7]u8 = @bitCast(a);
    return @bitCast(x);
}
pub fn main() void {
    var a: u8 = 0x11;
    var b: u32 = 0xAABBCCDD;
    var i: usize = 3;
    _ = .{ &a, &b, &i };
    const ct_from: u32 = comptime @bitCast(@as([3:7]u8, .{ 0x11, 2, 3 }));
    const ct_to: [3:7]u8 = comptime @bitCast(@as(u32, 0xAABBCCDD));
    const ct_rt: u32 = comptime @bitCast(@as([3:7]u8, @bitCast(@as(u32, 0xAABBCCDD))));
    std.debug.print("comptime: from {x} to[3] {x} roundtrip {x}\n", .{ ct_from, ct_to[i], ct_rt });
    std.debug.print("runtime:  from {x} to[3] {x} roundtrip {x}\n", .{ fromSent(a), toSent(b, i), roundTrip(b) });
}
```

Observed with stock Zig 0.17.1 (`x86_64-linux-musl` in Docker `linux/amd64` under Rosetta,
`aarch64-linux-musl` in a native `linux/arm64` container):

| evaluation | `from` | `to[3]` | `roundtrip` |
|---|---|---|---|
| comptime (every build) | `7030211` | `7` | `7bbccdd` |
| x86_64 Debug (self-hosted backend) | `7030211` | `aa` | `aabbccdd` |
| x86_64 Debug `-fllvm`, ReleaseSafe, ReleaseFast | `30211` | `0` | `bbccdd` |
| aarch64 Debug, ReleaseSafe, ReleaseFast (LLVM) | `30211` | `0` | `bbccdd` |

* Comptime: the source's sentinel is in the bits; the result's sentinel is the type's, the top
  8 bits of the operand are dropped.
* Self-hosted x86_64: a memory reinterpretation, the sentinel is one more item in both
  directions (the Zig ≤0.16 behaviour).
* LLVM: the source's sentinel is not in the bits (they are zero), and the result's sentinel item
  is not written: `[3:0x1234]u16` from `0x1111222233334444` reads `x[3]` as `0` in ReleaseSafe
  and as stack garbage (`bb`, `aabb`) in Debug on aarch64, never `0x1234` or `0x1111`.

Expected: one meaning. Either the sentinel is not part of the bit representation
(`@bitSizeOf([3:7]u8) == 24`, the result's sentinel is the type's), or it is, and a result whose
last item differs from the sentinel is checked illegal behaviour. In both cases the LLVM lowering
has to write the result's sentinel item.

## Related: Zig 0.14.1 leaves the sentinel of a runtime array initialization unwritten

```zig
noinline fn fromSent(a: u8) u32 {
    const x: [3:7]u8 = .{ a, 2, 3 };
    return @bitCast(x);
}
```

Zig 0.14.1 prints `11030211` (Debug) and `30211` (ReleaseSafe) for `fromSent(0x11)`; 0.15.2 and
0.16.0 print `7030211`. The 0.14.1 AIR stores items 0 to 2 through `ptr_elem_ptr` and has no
store of the sentinel; 0.15.2 and later store it. Fixed upstream in 0.15
(`sentInit` in `tests/roadmap/packed-casts/sentinel_arrays.zig`).
