const std = @import("std");
const source = @import("thread_tuple_source");

test "empty, ordered mixed, copied values, and shared atomic arguments" {
    try source.empty();
    try source.genericEmpty();
    const inputs = [_][3]u32{ .{ 1, 2, 4 }, .{ 9, 3, 17 }, .{ 0, 0, 0 }, .{ 0xffffffff, 7, 123 } };
    for (inputs) |values| {
        const a = values[0];
        const b = values[1];
        const c = values[2];
        try std.testing.expectEqual(a *% 52 +% b *% 80, try source.mixed(a, b));
        try std.testing.expectEqual(a *% 3 +% b *% 5 +% c *% 7 +% 99, try source.copied(a, b, c));
        try std.testing.expectEqual((a +% b) *% 3, try source.atomicShared(a, b));
    }
}

test "group empty and mixed argument tuples on Zig 0.16" {
    if (@hasDecl(std, "Io") and @hasDecl(std.Io, "Group")) {
        var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
        defer threaded.deinit();
        try std.testing.expectEqual(@as(u32, 680), try source.groupMixed(threaded.io(), 10, 2));
    }
}
