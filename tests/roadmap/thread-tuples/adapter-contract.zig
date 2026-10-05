//! Pending compiler-source regression: mutable captures and different alignments
//! call the same pure const-slice worker. Root validation exports this separately.
const std = @import("std");

fn sliceWorker(items: []align(1) const u64) void {
    if (items.len > 0 and items[0] == 0) @panic("zero item");
}

pub fn mutableCapture(items: []align(1) u64) !void {
    const child = try std.Thread.spawn(.{}, sliceWorker, .{items});
    child.join();
}

pub fn strongCapture(items: []align(8) const u64) !void {
    const child = try std.Thread.spawn(.{}, sliceWorker, .{items});
    child.join();
}

pub fn weakCapture(items: []align(1) const u64) !void {
    const child = try std.Thread.spawn(.{}, sliceWorker, .{items});
    child.join();
}

comptime {
    _ = &mutableCapture;
    _ = &strongCapture;
    _ = &weakCapture;
}
