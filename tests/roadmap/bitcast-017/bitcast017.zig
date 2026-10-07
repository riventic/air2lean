//! Zig 0.17.0 `@bitCast` in logical bit order (docs/bitcast-semantics.md). Values are the
//! 0.17.0 behaviour tests' (test/behavior/bitcast.zig) and the native probes'.
const std = @import("std");
const expectEqual = std.testing.expectEqual;

pub const E = enum(u8) { a, b, c };
pub const P = packed struct(u16) { foo: u5, bar: i7, baz: u3, qux: bool };

pub fn vecToInt(v: @Vector(4, u5)) u20 {
    return @bitCast(v);
}
pub fn intToVec(x: u20) @Vector(4, u5) {
    return @bitCast(x);
}
pub fn vecToArray(v: @Vector(4, u5)) [5]u4 {
    return @bitCast(v);
}
pub fn boolsToInt(v: @Vector(16, bool)) u16 {
    return @bitCast(v);
}
pub fn packedToBits(p: P) [16]u1 {
    return @bitCast(p);
}
pub fn paddedToInt(a: [2]u24) u48 {
    return @bitCast(a);
}
pub fn intToPadded(x: u48) [2]u24 {
    return @bitCast(x);
}
pub fn bytesToInt(a: [4]u8) u32 {
    return @bitCast(a);
}
pub fn intToEnum(x: u8) E {
    return @bitCast(x);
}
pub fn enumToSigned(e: E) i8 {
    return @bitCast(e);
}

test "logical bit order" {
    try expectEqual(@as(u20, 0x65e2), vecToInt(.{ 2, 15, 25, 0 }));
    try expectEqual([4]u5{ 2, 31, 18, 1 }, @as([4]u5, intToVec(0x0cbe2)));
    try expectEqual([5]u4{ 2, 14, 5, 6, 0 }, vecToArray(.{ 2, 15, 25, 0 }));
    var bools: @Vector(16, bool) = @splat(true);
    bools[1] = false;
    try expectEqual(@as(u16, 0xfffd), boolsToInt(bools));
    try expectEqual([16]u1{ 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1 },
        packedToBits(.{ .foo = 0b01001, .bar = -2, .baz = 0b010, .qux = true }));
    try expectEqual(@as(u48, 0x445566112233), paddedToInt(.{ 0x112233, 0x445566 }));
    try expectEqual([2]u24{ 0x112233, 0x445566 }, intToPadded(0x445566112233));
    try expectEqual(@as(u32, 0x44332211), bytesToInt(.{ 0x11, 0x22, 0x33, 0x44 }));
    try expectEqual(E.b, intToEnum(1));
    try expectEqual(@as(i8, 2), enumToSigned(.c));
}

comptime {
    _ = &vecToInt;
    _ = &intToVec;
    _ = &vecToArray;
    _ = &boolsToInt;
    _ = &packedToBits;
    _ = &paddedToInt;
    _ = &intToPadded;
    _ = &bytesToInt;
    _ = &intToEnum;
    _ = &enumToSigned;
}
