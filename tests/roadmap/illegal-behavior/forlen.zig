//! Multi-operand `for` loops with runtime safety off whose later operand is a range or an array
//! (docs/illegal-behavior.md row 27), exported by every supported Zig version (`for-air/<version>/`).
//! Only the patched Sema's `unreach` check (zig-patch hook.patch) carries the operand's length.

/// A slice and a range from 0: the range's length is its end, which has no instruction of its own.
pub fn forRange(a: []const u32, n: usize) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a, 0..n) |x, i| sum +%= x +% @as(u32, @truncate(i));
    return sum;
}

/// A slice and a range that does not start at 0.
pub fn forRangeFrom(a: []const u32, lo: usize, hi: usize) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a, lo..hi) |x, i| sum +%= x +% @as(u32, @truncate(i));
    return sum;
}

/// A slice and an array: the array's comptime length bounds the loop.
pub fn forArray(a: []const u32, b: *const [3]u32) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a, b) |x, y| sum +%= x +% y;
    return sum;
}

comptime {
    _ = &forRange;
    _ = &forRangeFrom;
    _ = &forArray;
}
