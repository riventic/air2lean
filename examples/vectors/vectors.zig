//! SIMD vector functions over @Vector(4, T) (16 bytes, the ABI round-up to a power of 2 is a
//! no-op here): a float dot product (elementwise mul, then a reduce add), a wrapping u32 dot
//! product, a saturating add, a max reduction, a lane shuffle (reverse), and a checked add that
//! can overflow in one lane. Bodies are fixed — Proofs/Vectors depends on them exactly; do not
//! reformat.

const std = @import("std");

export fn fDot(a: @Vector(4, f32), b: @Vector(4, f32)) f32 {
    return @reduce(.Add, a * b);
}

export fn uDotWrap(a: @Vector(4, u32), b: @Vector(4, u32)) u32 {
    return @reduce(.Add, a *% b);
}

export fn satAdd(a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32) {
    return a +| b;
}

export fn maxLane(v: @Vector(4, i32)) i32 {
    return @reduce(.Max, v);
}

export fn reverse(v: @Vector(4, u32)) @Vector(4, u32) {
    return @shuffle(u32, v, undefined, [4]i32{ 3, 2, 1, 0 });
}

export fn checkedAdd(a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32) {
    return a + b;
}

test "fDot" {
    try std.testing.expectEqual(@as(f32, 32.0), fDot(.{ 1, 2, 3, 4 }, .{ 4, 3, 2, 1 }));
}

test "uDotWrap" {
    try std.testing.expectEqual(@as(u32, 32), uDotWrap(.{ 1, 2, 3, 4 }, .{ 4, 3, 2, 1 }));
}

test "satAdd" {
    try std.testing.expectEqual(
        @as(@Vector(4, u32), .{ std.math.maxInt(u32), 3, 3, 3 }),
        satAdd(.{ std.math.maxInt(u32), 1, 2, 3 }, .{ 1, 1, 1, 0 }),
    );
}

test "maxLane" {
    try std.testing.expectEqual(@as(i32, 9), maxLane(.{ 1, 9, -3, 4 }));
}

test "reverse" {
    try std.testing.expectEqual(@as(@Vector(4, u32), .{ 4, 3, 2, 1 }), reverse(.{ 1, 2, 3, 4 }));
}

test "checkedAdd" {
    try std.testing.expectEqual(
        @as(@Vector(4, u32), .{ 2, 4, 6, 8 }),
        checkedAdd(.{ 1, 2, 3, 4 }, .{ 1, 2, 3, 4 }),
    );
}
