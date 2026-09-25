//! Float ops: one dispatch per width (op16/op32/op64/op80/op128; `sel` chooses the op),
//! plus cmp64 (comparison bitmask) and divExact64. docs/floats.md documents each op's
//! semantics and the reference target.

const std = @import("std");

/// `sel` picks the op; an unlisted `sel` returns `a` unchanged. One generic body shared by
/// every width, so op16/op32/... below stay one line each.
inline fn opFor(comptime T: type, sel: u8, a: T, b: T, c: T) T {
    return switch (sel) {
        0 => a + b,
        1 => a - b,
        2 => a * b,
        3 => a / b,
        4 => @mulAdd(T, a, b, c),
        5 => @divTrunc(a, b),
        6 => @divFloor(a, b),
        7 => @rem(a, b),
        8 => @mod(a, b),
        9 => @sqrt(a),
        10 => @floor(a),
        11 => @ceil(a),
        12 => @trunc(a),
        13 => @round(a),
        14 => @abs(a),
        15 => -a,
        16 => @min(a, b),
        17 => @max(a, b),
        18 => @sin(a),
        19 => @cos(a),
        20 => @tan(a),
        21 => @exp(a),
        22 => @exp2(a),
        23 => @log(a),
        24 => @log2(a),
        25 => @log10(a),
        else => a,
    };
}

pub fn op16(sel: u8, a: f16, b: f16, c: f16) f16 {
    return opFor(f16, sel, a, b, c);
}
pub fn op32(sel: u8, a: f32, b: f32, c: f32) f32 {
    return opFor(f32, sel, a, b, c);
}
pub fn op64(sel: u8, a: f64, b: f64, c: f64) f64 {
    return opFor(f64, sel, a, b, c);
}
pub fn op80(sel: u8, a: f80, b: f80, c: f80) f80 {
    return opFor(f80, sel, a, b, c);
}
pub fn op128(sel: u8, a: f128, b: f128, c: f128) f128 {
    return opFor(f128, sel, a, b, c);
}

/// Comparison bitmask: bit0 `<`, bit1 `<=`, bit2 `==`, bit3 `!=`, bit4 `>=`, bit5 `>`.
pub fn cmp64(a: f64, b: f64) u8 {
    var m: u8 = 0;
    if (a < b) m |= 1 << 0;
    if (a <= b) m |= 1 << 1;
    if (a == b) m |= 1 << 2;
    if (a != b) m |= 1 << 3;
    if (a >= b) m |= 1 << 4;
    if (a > b) m |= 1 << 5;
    return m;
}

pub fn divExact64(a: f64, b: f64) f64 {
    return @divExact(a, b);
}

comptime {
    _ = &op16;
    _ = &op32;
    _ = &op64;
    _ = &op80;
    _ = &op128;
    _ = &cmp64;
    _ = &divExact64;
}

test "op64 arithmetic" {
    try std.testing.expectEqual(@as(f64, 5.0), op64(0, 2.0, 3.0, 0));
    try std.testing.expectEqual(@as(f64, -1.0), op64(1, 2.0, 3.0, 0));
    try std.testing.expectEqual(@as(f64, 6.0), op64(2, 2.0, 3.0, 0));
    try std.testing.expectEqual(@as(f64, 2.0), op64(3, 4.0, 2.0, 0));
    try std.testing.expectEqual(@as(f64, 7.0), op64(4, 2.0, 3.0, 1.0));
}

test "op64 rounding and sign" {
    try std.testing.expectEqual(@as(f64, 2.0), op64(10, 2.9, 0, 0)); // floor
    try std.testing.expectEqual(@as(f64, 3.0), op64(11, 2.1, 0, 0)); // ceil
    try std.testing.expectEqual(@as(f64, 3.0), op64(13, 2.5, 0, 0)); // round, ties away
    try std.testing.expectEqual(@as(f64, 2.0), op64(14, -2.0, 0, 0)); // abs
    try std.testing.expectEqual(@as(f64, -2.0), op64(15, 2.0, 0, 0)); // neg
    try std.testing.expectEqual(@as(f64, 1.0), op64(16, 1.0, 2.0, 0)); // min
    try std.testing.expectEqual(@as(f64, 2.0), op64(17, 1.0, 2.0, 0)); // max
}

test "op64 unknown sel returns a" {
    try std.testing.expectEqual(@as(f64, 9.0), op64(255, 9.0, 0, 0));
}

test "cmp64" {
    try std.testing.expectEqual(@as(u8, 0), cmp64(1.0, 2.0) & (1 << 4)); // not >=
    try std.testing.expect(cmp64(1.0, 2.0) & (1 << 0) != 0); // <
    try std.testing.expect(cmp64(2.0, 2.0) & (1 << 1) != 0); // <=
    try std.testing.expect(cmp64(2.0, 2.0) & (1 << 2) != 0); // ==
    try std.testing.expect(cmp64(2.0, 1.0) & (1 << 5) != 0); // >
    try std.testing.expectEqual(@as(u8, 1 << 3), cmp64(std.math.nan(f64), 1.0)); // NaN: only !=
}

test "divExact64" {
    try std.testing.expectEqual(@as(f64, 2.0), divExact64(6.0, 3.0));
}
