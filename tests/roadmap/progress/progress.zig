//! C03 source integration: `spinLoopHint` lives in std.atomic in supported Zig versions.
const std = @import("std");

pub fn spinOnce() void {
    std.atomic.spinLoopHint();
}

pub fn yieldOnce() std.Thread.YieldError!void {
    try std.Thread.yield();
}

/// Idle-worker safety example. This has no eventual-completion contract.
pub fn idle(flag: *const u32) void {
    while (@atomicLoad(u32, flag, .acquire) == 0) {
        std.atomic.spinLoopHint();
        std.Thread.yield() catch {};
    }
}

pub fn catchesYield() bool {
    std.Thread.yield() catch return false;
    return true;
}

comptime {
    _ = &spinOnce;
    _ = &yieldOnce;
    _ = &idle;
    _ = &catchesYield;
}
