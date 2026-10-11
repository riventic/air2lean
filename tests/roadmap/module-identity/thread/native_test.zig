// Native reference for check.sh: what Zig computes for `entry` (`7 + x`, wrapping).
const std = @import("std");
const main = @import("main.zig");

test "entry calls the user Thread.spawn" {
    try std.testing.expectEqual(@as(u32, 12), main.entry(5));
    try std.testing.expectEqual(@as(u32, 6), main.entry(0xFFFFFFFF));
}
