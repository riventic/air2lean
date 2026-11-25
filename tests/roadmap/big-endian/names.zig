//! T03: `@tagName` and `@errorName` at both byte orders. A name is a `[:0]const u8` into a
//! static block whose bytes are the same at both orders; a slice stored in memory has its
//! `usize` length at the profile's order. Exported for s390x-linux, mips64-linux and
//! x86_64-linux (exports.json); `test` runs natively (check.sh --native).
const std = @import("std");

pub const Color = enum { red, green, blue };

pub fn colorName(c: Color) [:0]const u8 {
    return @tagName(c);
}

/// A non-exhaustive enum with a two-byte tag: an unnamed value has no tag name (a safety panic).
pub const Level = enum(u16) { low = 1, high = 0x1234, _ };

pub fn levelName(l: Level) [:0]const u8 {
    return @tagName(l);
}

pub const Fault = error{ Empty, TooLong };

pub fn faultName(e: Fault) [:0]const u8 {
    return @errorName(e);
}

/// Byte `i` of a name, bounds-checked against the name's length (index `len` is the sentinel).
pub fn nameByte(c: Color, i: usize) u8 {
    return @tagName(c)[i];
}

/// Byte `i` of the length of a name slice stored in memory: the length is the last of its 8
/// bytes at big endian, the first at little endian.
pub fn storedLenByte(c: Color, i: usize) u8 {
    var s: []const u8 = @tagName(c);
    const bytes: *const [2 * @sizeOf(usize)]u8 = @ptrCast(&s);
    return bytes[@sizeOf(usize) + i];
}

comptime {
    _ = &colorName;
    _ = &levelName;
    _ = &faultName;
    _ = &nameByte;
    _ = &storedLenByte;
}

test "names" {
    const big = @import("builtin").cpu.arch.endian() == .big;
    try std.testing.expectEqualStrings("green", colorName(.green));
    try std.testing.expectEqualStrings("high", levelName(@enumFromInt(0x1234)));
    try std.testing.expectEqualStrings("TooLong", faultName(error.TooLong));
    try std.testing.expectEqual(@as(u8, 'l'), nameByte(.blue, 1));
    try std.testing.expectEqual(@as(u8, 0), nameByte(.blue, 4));
    try std.testing.expectEqual(@as(u8, 5), storedLenByte(.green, if (big) 7 else 0));
    try std.testing.expectEqual(@as(u8, 0), storedLenByte(.green, if (big) 0 else 7));
}
