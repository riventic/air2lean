const std = @import("std");
const wrappers = @import("flow_time_wrapper");

fn boundaries(comptime T: type, comptime add: anytype) !void {
    const max = std.math.maxInt(T);
    try std.testing.expectEqual(@as(T, 0), try add(0, 0));
    try std.testing.expectEqual(@as(T, 12), try add(5, 7));
    try std.testing.expectEqual(max - 1, try add(max - 2, 1));
    try std.testing.expectEqual(max - 1, try add(1, max - 2));
    try std.testing.expectError(error.TimeOverflow, add(max - 1, 1));
    try std.testing.expectError(error.TimeOverflow, add(1, max - 1));
    try std.testing.expectError(error.TimeOverflow, add(max, 0));
    try std.testing.expectError(error.TimeOverflow, add(max, 1));
    try std.testing.expectError(error.TimeOverflow, add(max - 1, 2));
    try std.testing.expectError(error.TimeOverflow, add(max, max));
}

test "Flow original timestamp32 boundaries" {
    try boundaries(u32, wrappers.timestamp32);
}

test "Flow original timestamp64 boundaries" {
    try boundaries(u64, wrappers.timestamp64);
}
