const std = @import("std");
const common = @import("common");
const source = @import("source.zig");

fn run(comptime sentinel: u8, name: []const u8, cap: usize, failures: []const usize,
    sizes: []const usize, expected: []const bool) !void {
    var ta: common.TestAllocator = .{ .request_cap = cap, .failures = failures };
    defer ta.live.deinit(std.heap.page_allocator);
    for (sizes, expected, 0..) |n, want, i| {
        const result = if (sentinel == 0) source.makeZero(ta.allocator(), n)
            else source.makeByte(ta.allocator(), n);
        if (result) |s| {
            if (!want or s.len != n or ta.live.items.len != 1 or ta.live.items[0].len != n + 1)
                return error.SentinelOwnershipMismatch;
            if (s.ptr[n] != sentinel) return error.SentinelMismatch;
            for (s, 0..) |*b, j| b.* = @truncate(j + 7);
            for (s, 0..) |b, j| if (b != @as(u8, @truncate(j + 7))) return error.PayloadMismatch;
            if (s.ptr[n] != sentinel) return error.SentinelMismatch;
            if (sentinel == 0) source.releaseZero(ta.allocator(), s) else source.releaseByte(ta.allocator(), s);
        } else |err| {
            if (want or err != error.OutOfMemory) return error.FailureMismatch;
        }
        if (ta.live.items.len != 0 or ta.count != i + 1) return error.CleanupMismatch;
        std.debug.print("{s} {d} {d} {d} 0\n", .{ name, i, @intFromBool(want), ta.count });
    }
}
pub fn main() !void {
    try run(0, "zero-sentinel", 64, &.{}, &.{0, 1, 8}, &.{true, true, true});
    try run(42, "nonzero-sentinel", 64, &.{}, &.{0, 1, 8}, &.{true, true, true});
    try run(42, "repeated-failure", 64, &.{0, 2}, &.{0, 8, 0, 8}, &.{false, true, false, true});
    try run(42, "extra-byte-cap", 8, &.{}, &.{7, 8}, &.{true, false});
    try run(0, "empty-can-fail", 0, &.{}, &.{0}, &.{false});
}
