//! L07: a sentinel-terminated array in a Zig ≤0.16 `@bitCast`. `@bitSizeOf([n:s]T)` counts the
//! sentinel (`lenIncludingSentinel`), and the cast reinterprets memory, so the sentinel is one
//! more item: of the source's bits, and of the result (whose last item is then the source's
//! bits, not checked against the type's sentinel). Zig 0.17 is rejected
//! (`reject_sentinel.zig`, `docs/upstream/bitcast-sentinel-array.md`).

/// The sentinel is the top byte.
pub fn sentToInt(a: [3:7]u8) u32 {
    return @bitCast(a);
}

pub fn wideToInt(a: [3:0x1234]u16) u64 {
    return @bitCast(a);
}

/// Each inner array has its own sentinel item.
pub fn nestedToInt(a: [2][3:5]u8) u64 {
    return @bitCast(a);
}

/// The sentinel becomes item 3 of an array without one.
pub fn sentItem3(a: [3:9]u8) u8 {
    const b: [4]u8 = @bitCast(a);
    return b[3];
}

/// Item `i` of the array made from `x`; item 3 is the top byte of `x`, whatever the type's
/// sentinel is.
pub fn intToSentAt(x: u32, i: usize) u8 {
    const a: [3:0]u8 = @bitCast(x);
    return a[i];
}

/// The round trip keeps every bit, the sentinel item's too.
pub fn roundTrip(x: u32) u32 {
    const a: [3:0]u8 = @bitCast(x);
    return @bitCast(a);
}

comptime {
    _ = &sentToInt;
    _ = &wideToInt;
    _ = &nestedToInt;
    _ = &sentItem3;
    _ = &intToSentAt;
    _ = &roundTrip;
}
