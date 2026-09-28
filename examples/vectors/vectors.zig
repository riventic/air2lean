//! SIMD vector functions over @Vector(4, T) (16 bytes, the ABI round-up to a power of 2 is a
//! no-op here): a float dot product (elementwise mul, then a reduce add), a wrapping u32 dot
//! product, a saturating add, a max reduction, a lane shuffle (reverse), and a checked add that
//! can overflow in one lane; then one function per remaining vector op (coverage). Bodies are fixed — Proofs/Vectors depends on them exactly; do not
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

// Coverage of the other vector ops: `@splat`, `@select`, a shuffle from two vectors, the other
// `@reduce` kinds, and a vector in memory (an escaping local).

export fn splatAdd(v: @Vector(4, u32), s: u32) @Vector(4, u32) {
    const k: @Vector(4, u32) = @splat(s);
    return v +% k;
}

export fn pick(m: @Vector(4, bool), a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32) {
    return @select(u32, m, a, b);
}

export fn interleave(a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32) {
    return @shuffle(u32, a, b, [4]i32{ 0, ~@as(i32, 0), 1, ~@as(i32, 3) });
}

export fn andLanes(v: @Vector(4, u32)) u32 {
    return @reduce(.And, v);
}

export fn orLanes(v: @Vector(4, u32)) u32 {
    return @reduce(.Or, v);
}

export fn xorLanes(v: @Vector(4, u32)) u32 {
    return @reduce(.Xor, v);
}

export fn minLane(v: @Vector(4, i32)) i32 {
    return @reduce(.Min, v);
}

export fn uMinLane(v: @Vector(4, u32)) u32 {
    return @reduce(.Min, v);
}

export fn fMin(v: @Vector(4, f32)) f32 {
    return @reduce(.Min, v);
}

export fn fMax(v: @Vector(4, f32)) f32 {
    return @reduce(.Max, v);
}

fn addTo(p: *@Vector(4, u32), v: @Vector(4, u32)) void {
    p.* +%= v;
}

export fn twiceInMem(v: @Vector(4, u32)) @Vector(4, u32) {
    var acc: @Vector(4, u32) = v;
    addTo(&acc, v);
    return acc;
}

test "coverage" {
    const V = @Vector(4, u32);
    try std.testing.expectEqual(@as(V, .{ 3, 4, 5, 6 }), splatAdd(.{ 1, 2, 3, 4 }, 2));
    try std.testing.expectEqual(@as(V, .{ 1, 6, 3, 8 }), pick(.{ true, false, true, false }, .{ 1, 2, 3, 4 }, .{ 5, 6, 7, 8 }));
    try std.testing.expectEqual(@as(V, .{ 1, 5, 2, 8 }), interleave(.{ 1, 2, 3, 4 }, .{ 5, 6, 7, 8 }));
    try std.testing.expectEqual(@as(u32, 1), andLanes(.{ 3, 5, 7, 9 }));
    try std.testing.expectEqual(@as(u32, 15), orLanes(.{ 1, 2, 4, 8 }));
    try std.testing.expectEqual(@as(u32, 4), xorLanes(.{ 1, 2, 3, 4 }));
    try std.testing.expectEqual(@as(i32, -3), minLane(.{ 1, 9, -3, 4 }));
    try std.testing.expectEqual(@as(u32, 1), uMinLane(.{ 1, 9, 3, 4 }));
    try std.testing.expectEqual(@as(f32, -2), fMin(.{ 1, -2, 3, 0 }));
    try std.testing.expectEqual(@as(f32, 3), fMax(.{ 1, -2, 3, 0 }));
    try std.testing.expectEqual(@as(V, .{ 2, 4, 6, 8 }), twiceInMem(.{ 1, 2, 3, 4 }));
}

test "fDot" {
    try std.testing.expectEqual(@as(f32, 20.0), fDot(.{ 1, 2, 3, 4 }, .{ 4, 3, 2, 1 }));
}

test "uDotWrap" {
    try std.testing.expectEqual(@as(u32, 20), uDotWrap(.{ 1, 2, 3, 4 }, .{ 4, 3, 2, 1 }));
}

test "satAdd" {
    try std.testing.expectEqual(
        @as(@Vector(4, u32), .{ std.math.maxInt(u32), 2, 3, 3 }),
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
