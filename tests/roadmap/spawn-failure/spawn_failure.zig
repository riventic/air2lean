//! Public resource-failure clients. No private evaluator code or AIR is used.
const std = @import("std");
const Io = if (@hasDecl(std, "Io") and @hasDecl(std.Io, "Group")) std.Io else void;

fn writeWorker(out: *u32, value: u32) void {
    out.* = value;
}

/// If the second spawn fails, errdefer joins the first child before its capture dies.
pub fn threadPair(value: u32) !u32 {
    var left: u32 = 0;
    var right: u32 = 0;
    const first = try std.Thread.spawn(.{}, writeWorker, .{ &left, value });
    errdefer first.join();
    const second = try std.Thread.spawn(.{}, writeWorker, .{ &right, value +% 1 });
    first.join();
    second.join();
    return left +% right;
}

/// A failed spawn retains the untouched capture in the caller and has no join handle.
pub fn threadCatch(value: u32) u32 {
    var out: u32 = 0;
    const child = std.Thread.spawn(.{ .stack_size = 1024 * 1024 }, writeWorker, .{ &out, value }) catch {
        return out;
    };
    child.join();
    return out;
}

/// Group.async must also work when its task executes synchronously in this caller.
pub fn groupAsync(io: Io, value: u32) !u32 {
    var out: u32 = 0;
    var group: Io.Group = .init;
    group.async(io, writeWorker, .{ &out, value });
    try group.await(io);
    return out;
}

/// Concurrency failure must not execute or publish the rejected task.
pub fn groupConcurrent(io: Io, value: u32) !u32 {
    var out: u32 = 0;
    var group: Io.Group = .init;
    defer group.cancel(io);
    try group.concurrent(io, writeWorker, .{ &out, value });
    try group.await(io);
    return out;
}

comptime {
    _ = &threadPair;
    _ = &threadCatch;
    if (Io != void) {
        _ = &groupAsync;
        _ = &groupConcurrent;
    }
}
