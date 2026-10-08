//! T02: one source, exported for wasm32-freestanding, wasm32-wasi and x86_64-linux.
//! `usize` is 32 or 64 bits; pointers 4 or 8 bytes; a slice is pointer then length.
const std = @import("std");

/// The bytes of `n` `u32` items, or null when the product does not fit a `usize`.
pub fn byteCount(n: usize) ?usize {
    const r = @mulWithOverflow(n, @as(usize, 4));
    if (r[1] != 0) return null;
    return r[0];
}

/// `n + 1`, with the checked `usize` addition (overflow panics).
pub fn succ(n: usize) usize {
    return n + 1;
}

/// Item `i` (bounds-checked).
pub fn at(s: []const u32, i: usize) u32 {
    return s[i];
}

/// `n` zeroed items: `n * 4` bytes, `error.OutOfMemory` when that overflows a `usize`.
pub fn zeros(a: std.mem.Allocator, n: usize) ![]u32 {
    const b = try a.alloc(u32, n);
    @memset(b, 0);
    return b;
}

pub fn release(a: std.mem.Allocator, b: []u32) void {
    a.free(b);
}

/// A pointer and a slice in memory: 12 bytes on wasm32, 24 bytes on x86_64.
pub const View = struct { first: *u32, rest: []u32 };

/// The length field of a slice in memory: offset 8 on wasm32 (after a 4-byte pointer and the
/// slice's own 4-byte pointer), 16 on x86_64.
pub fn restLen(v: *const View) usize {
    return v.rest.len;
}

/// A pointer loaded from memory, then a store through it.
pub fn setFirst(v: *View, x: u32) void {
    v.first.* = x;
}

/// The byte distance of item `i` from item 0 (`@intFromPtr`).
pub fn offsetOf(s: []u32, i: usize) usize {
    return @intFromPtr(&s[i]) - @intFromPtr(s.ptr);
}

/// An array as a slice (the length is a `usize` constant) and `@memcpy`.
pub fn copy4(dst: *[4]u8, src: *const [4]u8) void {
    const d: []u8 = dst;
    @memcpy(d, src);
}

// The layouts that the model checks (`modelLayout`), evaluated by the compiler for the target.
comptime {
    std.debug.assert(@sizeOf(usize) == @sizeOf(*u32));
    std.debug.assert(@sizeOf([]u32) == 2 * @sizeOf(usize) and @alignOf([]u32) == @sizeOf(usize));
    std.debug.assert(@sizeOf(?*u32) == @sizeOf(usize));
    std.debug.assert(@sizeOf(std.mem.Allocator) == 2 * @sizeOf(usize));
    std.debug.assert(@sizeOf(View) == 3 * @sizeOf(usize));
    std.debug.assert(@offsetOf(View, "rest") == @sizeOf(usize));
}

comptime {
    _ = &byteCount;
    _ = &succ;
    _ = &at;
    _ = &zeros;
    _ = &release;
    _ = &restLen;
    _ = &setFirst;
    _ = &offsetOf;
    _ = &copy4;
}

test "byteCount boundary" {
    const max_items = std.math.maxInt(usize) / 4;
    try std.testing.expectEqual(@as(?usize, max_items * 4), byteCount(max_items));
    try std.testing.expectEqual(@as(?usize, null), byteCount(max_items + 1));
}

test "layouts" {
    try std.testing.expectEqual(@as(usize, 2 * @sizeOf(usize)), @sizeOf([]u32));
    try std.testing.expectEqual(@as(usize, 3 * @sizeOf(usize)), @sizeOf(View));
    try std.testing.expectEqual(@as(usize, @sizeOf(usize)), @offsetOf(View, "rest"));
}
