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

const SemCounter = struct {
    io: Io,
    s: Io.Semaphore = .{ .permits = 1 },
    n: u32 = 0,
};

fn semWork(c: *SemCounter) void {
    for (0..2) |_| {
        c.s.waitUncancelable(c.io);
        defer c.s.post(c.io);
        c.n += 1;
    }
}

/// Two threads add 2 each to a counter under an `Io.Semaphore` with one permit: always 4.
pub fn semaphoreCounter(io: Io) !u32 {
    var c: SemCounter = .{ .io = io };
    const t = try std.Thread.spawn(.{}, semWork, .{&c});
    semWork(&c);
    t.join();
    return c.n;
}

const Shared = struct {
    io: Io,
    l: Io.RwLock = .init,
    n: u32 = 0,
};

fn writer(sh: *Shared) void {
    for (0..2) |_| {
        sh.l.lockUncancelable(sh.io);
        defer sh.l.unlock(sh.io);
        sh.n += 1;
    }
}

fn readShared(sh: *Shared) u32 {
    sh.l.lockSharedUncancelable(sh.io);
    defer sh.l.unlockShared(sh.io);
    return sh.n;
}

/// A writer adds 1 two times under an `Io.RwLock`; the main thread reads under the shared lock
/// while it runs and after the join: `10 * first + last`, first 0, 1 or 2, last always 2.
pub fn rwLockRead(io: Io) !u32 {
    var sh: Shared = .{ .io = io };
    const t = try std.Thread.spawn(.{}, writer, .{&sh});
    const first = readShared(&sh);
    t.join();
    return 10 * first + readShared(&sh);
}

/// A second shared-lock client: both observations occur during one shared hold.
/// The writer still runs twice; successful results are 0, 11 or 22.
pub fn rwLockSnapshotPair(io: Io) !u32 {
    var sh: Shared = .{ .io = io };
    const t = try std.Thread.spawn(.{}, writer, .{&sh});
    sh.l.lockSharedUncancelable(io);
    const first = sh.n;
    const second = sh.n;
    sh.l.unlockShared(io);
    t.join();
    return 10 * first + second;
}

comptime {
    _ = &mutexCounter;
    _ = &handoff;
    _ = &semaphoreCounter;
    _ = &rwLockRead;
    _ = &rwLockSnapshotPair;
}
