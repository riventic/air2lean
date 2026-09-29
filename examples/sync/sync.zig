//! T3: the std sync primitives of Zig 0.16.0 (`std.Io`), translated from their std code; the
//! futex under them is the model (`docs/std-models.md` §Thread model).

const std = @import("std");
const Io = std.Io;

const Counter = struct {
    io: Io,
    m: Io.Mutex = .init,
    n: u32 = 0,
};

fn work(c: *Counter) void {
    for (0..2) |_| {
        c.m.lockUncancelable(c.io);
        defer c.m.unlock(c.io);
        c.n += 1;
    }
}

/// Two threads add 2 each to a counter under an `Io.Mutex`: always 4.
pub fn mutexCounter(io: Io) !u32 {
    var c: Counter = .{ .io = io };
    const t = try std.Thread.spawn(.{}, work, .{&c});
    work(&c);
    t.join();
    return c.n;
}

comptime {
    _ = &mutexCounter;
}
