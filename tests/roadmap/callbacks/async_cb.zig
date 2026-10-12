//! E02 fixture: a callback called from a spawned thread (an asynchronous callback), bound to a
//! registry contract through its address (`&ext_visit`).
const std = @import("std");

extern fn ext_visit(ctx: *u32, x: u32) callconv(.c) bool;

pub const Visitor = *const fn (*u32, u32) callconv(.c) bool;

fn worker(cb: Visitor, ctx: *u32, x: u32) void {
    _ = cb(ctx, x);
}

/// A spawned thread and the caller each call `cb`, on their own contexts.
pub fn runBoth(cb: Visitor, a: *u32, b: *u32, x: u32) !void {
    const t = try std.Thread.spawn(.{}, worker, .{ cb, a, x });
    worker(cb, b, x);
    t.join();
}

pub fn runExternal(a: *u32, b: *u32, x: u32) !void {
    try runBoth(&ext_visit, a, b, x);
}

comptime {
    _ = &runExternal;
}
