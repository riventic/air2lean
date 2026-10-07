const std = @import("std");
const common = @import("common");
const source = @import("source.zig");

const Op = union(enum) { append: u8, resize: usize };

/// One observation: outcome, length, defined payload prefix, terminator byte, allocation
/// attempts and live blocks after the operation, live blocks after release. `TestAllocator`
/// remap always fails, as the model's default policy; realloc then allocates, copies and frees.
fn run(name: []const u8, cap: usize, failures: []const usize, n: usize, op: Op) !void {
    var ta: common.TestAllocator = .{ .request_cap = cap, .failures = failures };
    defer ta.live.deinit(std.heap.page_allocator);
    const a = ta.allocator();
    var s = try source.make(a, n);
    for (s, 0..) |*b, i| b.* = @truncate(0x61 + i);
    const result: error{OutOfMemory}![:0]u8 = switch (op) {
        .append => |c| source.append(a, s, c),
        .resize => |k| source.resize(a, s, k),
    };
    var ok = true;
    if (result) |g| s = g else |_| ok = false;
    const defined = switch (op) {
        .append => if (ok) s.len else n,
        .resize => @min(n, s.len),
    };
    var payload: [64]u8 = undefined;
    var k: usize = 0;
    for (s[0..defined]) |b| {
        _ = std.fmt.bufPrint(payload[k..][0..2], "{x:0>2}", .{b}) catch unreachable;
        k += 2;
    }
    if (k == 0) {
        payload[0] = '-';
        k = 1;
    }
    const allocs = ta.count;
    const live = ta.live.items.len;
    const len = s.len;
    const term = s[s.len];
    source.release(a, s);
    std.debug.print("{s} {s} {d} {s} {x:0>2} {d} {d} {d}\n", .{ name, if (ok) "ok" else "oom", len, payload[0..k], term, allocs, live, ta.live.items.len });
}

pub fn main() !void {
    try run("append", 64, &.{}, 3, .{ .append = 0x64 });
    try run("append-empty", 64, &.{}, 0, .{ .append = 0x78 });
    try run("append-fail", 64, &.{1}, 3, .{ .append = 0x64 });
    try run("append-cap", 4, &.{}, 3, .{ .append = 0x64 });
    try run("shrink", 64, &.{}, 4, .{ .resize = 2 });
    try run("shrink-empty", 64, &.{}, 3, .{ .resize = 0 });
    try run("grow", 64, &.{}, 2, .{ .resize = 4 });
    try run("same", 64, &.{}, 2, .{ .resize = 2 });
    try run("resize-fail", 64, &.{1}, 4, .{ .resize = 2 });
}
