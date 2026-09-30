//! T3c: `std.Io.Group` (Zig 0.16.0): tasks that a group runs, then an `await` of all of them.
//! The model runs each task as a thread (`docs/std-models.md` §Thread model); `Io.Mutex` is
//! translated from its std code.

const std = @import("std");
const Io = std.Io;

const Counter = struct {
    io: Io,
    m: Io.Mutex = .init,
    n: u32 = 0,
};

fn add(c: *Counter) void {
    c.m.lockUncancelable(c.io);
    defer c.m.unlock(c.io);
    c.n += 1;
}

/// Three tasks in an `Io.Group` add 1 each under an `Io.Mutex`; after `await`: always 3.
pub fn groupCounter(io: Io) !u32 {
    var c: Counter = .{ .io = io };
    var g: Io.Group = .init;
    for (0..3) |_| g.async(io, add, .{&c});
    try g.await(io);
    return c.n;
}

/// The same with `Group.concurrent` and `Group.cancel` (the model never cancels, so `cancel`
/// waits for the tasks as `await` does): always 2.
pub fn groupConcurrent(io: Io) !u32 {
    var c: Counter = .{ .io = io };
    var g: Io.Group = .init;
    for (0..2) |_| try g.concurrent(io, add, .{&c});
    g.cancel(io);
    return c.n;
}

comptime {
    _ = &groupCounter;
    _ = &groupConcurrent;
}
