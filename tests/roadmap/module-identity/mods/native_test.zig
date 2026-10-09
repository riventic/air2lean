// Native reference for check.sh: what Zig computes for `entry` (`(x+1) + 3x`, wrapping).
const std = @import("std");
const main = @import("main.zig");

test "entry uses both helpers" {
    try std.testing.expectEqual(@as(u32, 21), main.entry(5));
    try std.testing.expectEqual(@as(u32, 0xFFFFFFFD), main.entry(0xFFFFFFFF));
}
