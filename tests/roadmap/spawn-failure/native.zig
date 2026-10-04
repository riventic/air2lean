const std = @import("std");
const source = @import("spawn_failure_source");

fn allowedSpawnError(err: anyerror) bool {
    return switch (err) {
        error.ThreadQuotaExceeded, error.SystemResources, error.OutOfMemory,
        error.LockedMemoryLimitExceeded, error.Unexpected => true,
        else => false,
    };
}

test "native thread outcomes are allowed, without requiring failure frequency" {
    for ([_]u32{ 1, 7, 0xfffffffe }) |value| {
        if (source.threadPair(value)) |result| {
            try std.testing.expectEqual(value +% value +% 1, result);
        } else |err| {
            try std.testing.expect(allowedSpawnError(err));
        }
        const caught = source.threadCatch(value);
        try std.testing.expect(caught == 0 or caught == value);
    }
}

test "group eager fallback and concurrent assignment have different contracts" {
    if (@hasDecl(std, "Io") and @hasDecl(std.Io, "Group")) {
        var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
        defer threaded.deinit();
        try std.testing.expectEqual(@as(u32, 19), try source.groupAsync(threaded.io(), 19));
        if (source.groupConcurrent(threaded.io(), 23)) |result| {
            try std.testing.expectEqual(@as(u32, 23), result);
        } else |err| {
            try std.testing.expect(err == error.ConcurrencyUnavailable);
        }
    }
}
