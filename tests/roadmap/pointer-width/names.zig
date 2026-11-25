//! T02: `@tagName` and `@errorName` under both pointer widths. Each returns a `[:0]const u8`
//! into a static name: on wasm32 a 4-byte pointer and a 32-bit `usize` length, on x86_64 an
//! 8-byte pointer and a 64-bit length. Exported for wasm32-freestanding, wasm32-wasi and
//! x86_64-linux (exports.json).
const std = @import("std");

pub const Color = enum { red, green, blue };

pub fn colorName(c: Color) [:0]const u8 {
    return @tagName(c);
}

/// A non-exhaustive enum: an unnamed value has no tag name (a safety panic).
pub const Level = enum(u8) { low = 1, high = 200, _ };

pub fn levelName(l: Level) [:0]const u8 {
    return @tagName(l);
}

pub const Fault = error{ Empty, TooLong };

pub fn faultName(e: Fault) [:0]const u8 {
    return @errorName(e);
}

/// Byte `i` of a tag name, bounds-checked against the name's `usize` length.
pub fn nameByte(c: Color, i: usize) u8 {
    return @tagName(c)[i];
}

comptime {
    _ = &colorName;
    _ = &levelName;
    _ = &faultName;
    _ = &nameByte;
}

test "names" {
    try std.testing.expectEqualStrings("green", colorName(.green));
    try std.testing.expectEqual(@as(usize, 5), colorName(.green).len);
    try std.testing.expectEqual(@as(u8, 0), colorName(.green)[5]);
    try std.testing.expectEqualStrings("high", levelName(@enumFromInt(200)));
    try std.testing.expectEqualStrings("TooLong", faultName(error.TooLong));
    try std.testing.expectEqual(@as(u8, 'l'), nameByte(.blue, 1));
}
