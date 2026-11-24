//! L07, rejected: a sentinel-terminated array in a Zig 0.17 `@bitCast`. Its comptime evaluation,
//! the LLVM backend and the self-hosted x86_64 backend give the sentinel's bits three different
//! meanings (`docs/upstream/bitcast-sentinel-array.md`), so no model equals the native result.
//! Each function is translated alone and must be rejected (`check.sh`).

pub fn sentToInt(a: [3:7]u8) u32 {
    return @bitCast(a);
}

pub fn intToSentAt(x: u32, i: usize) u8 {
    const a: [3:7]u8 = @bitCast(x);
    return a[i];
}

/// A sentinel array as an element.
pub fn nestedToInt(a: [2][3:5]u8) u64 {
    return @bitCast(a);
}

pub fn sentToArray(a: [3:9]u8) [4]u8 {
    return @bitCast(a);
}

comptime {
    _ = &sentToInt;
    _ = &intToSentAt;
    _ = &nestedToInt;
    _ = &sentToArray;
}
