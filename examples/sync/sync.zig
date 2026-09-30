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

const Box = struct {
    io: Io,
    m: Io.Mutex = .init,
    c: Io.Condition = .init,
    ready: bool = false,
    done: Io.Event = .unset,
    v: u32 = 0,
};

fn producer(b: *Box) void {
    b.m.lockUncancelable(b.io);
    b.v = 7;
    b.ready = true;
    b.m.unlock(b.io);
    b.c.signal(b.io);
    b.done.set(b.io);
}

/// A hand-off: the main thread waits on an `Io.Condition` until the producer has set the value,
/// then on an `Io.Event`. Always 7.
pub fn handoff(io: Io) !u32 {
    var b: Box = .{ .io = io };
    const t = try std.Thread.spawn(.{}, producer, .{&b});
    b.m.lockUncancelable(io);
    while (!b.ready) b.c.waitUncancelable(io, &b.m);
    const v = b.v;
    b.m.unlock(io);
    b.done.waitUncancelable(io);
    t.join();
    return v;
}

comptime {
    _ = &mutexCounter;
    _ = &handoff;
}
