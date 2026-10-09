//! C08 native check: the stock Zig 0.16.0 `Io.Threaded` gives the outcomes that the model and
//! the proofs allow, with assigned tasks and with every task run eagerly in the caller.
const std = @import("std");
const source = @import("futures_source");

fn check(io: std.Io) !void {
    for ([_]u32{ 0, 1, 7, 65536, 0xffffffff }) |x| {
        try std.testing.expectEqual(x *% x, source.awaitValue(io, x));
        try std.testing.expectEqual(x *% x +% x *% x, source.awaitTwice(io, x));
        try std.testing.expectEqual(x, source.awaitOwned(io, x));
        if (source.cancelValue(io, x)) |v| {
            try std.testing.expectEqual(x +% 1, v);
        } else |err| {
            try std.testing.expectEqual(error.Canceled, err);
        }
    }
    try std.testing.expectError(error.Zero, source.awaitError(io, 0));
    try std.testing.expectEqual(@as(u32, 4), try source.awaitError(io, 5));
}

test "assigned futures" {
    var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
    defer threaded.deinit();
    try check(threaded.io());
}

test "eager futures (async limit zero)" {
    var eager: std.Io.Threaded = .init(std.heap.page_allocator, .{ .async_limit = .nothing });
    defer eager.deinit();
    try check(eager.io());
}
