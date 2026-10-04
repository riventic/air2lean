//! T3c: the sync primitives of `std.Thread` (Zig 0.15.2), translated from their std code. The
//! OS boundary under them is the model (`docs/std-models.md` §Thread model): `Thread.Futex` on
//! Linux, and `os_unfair_lock` for `Thread.Mutex` on macOS. The std code of `Thread.Mutex`
//! differs by OS, so its translation does too (`tests/golden/0.15.2/threadsync/Gen-darwin.lean`).

const std = @import("std");
const Thread = std.Thread;

const Counter = struct {
    m: Thread.Mutex = .{},
    n: u32 = 0,
};

fn work(c: *Counter) void {
    for (0..2) |_| {
        c.m.lock();
        defer c.m.unlock();
        c.n += 1;
    }
}

/// Two threads add 2 each to a counter under a `Thread.Mutex`: always 4.
pub fn mutexCounter() !u32 {
    var c: Counter = .{};
    const t = try Thread.spawn(.{}, work, .{&c});
    work(&c);
    t.join();
    return c.n;
}

const Box = struct {
    m: Thread.Mutex = .{},
    c: Thread.Condition = .{},
    ready: bool = false,
    done: Thread.ResetEvent = .{},
    v: u32 = 0,
};

fn producer(b: *Box) void {
    b.m.lock();
    b.v = 7;
    b.ready = true;
    b.m.unlock();
    b.c.signal();
    b.done.set();
}

/// A hand-off: the main thread waits on a `Thread.Condition` until the producer has set the
/// value, then on a `Thread.ResetEvent`. Always 7. The main thread reads the fields through a
/// pointer: 0.15.2 lowers a field read of a local struct (`b.ready`) as a load of the whole
/// struct, which the model reads as it is written, so it would race with the producer's atomics
/// on the other fields (`docs/std-models.md` §Thread model).
pub fn handoff() !u32 {
    var b: Box = .{};
    const bp = &b;
    const t = try Thread.spawn(.{}, producer, .{bp});
    bp.m.lock();
    while (!bp.ready) bp.c.wait(&bp.m);
    const v = bp.v;
    bp.m.unlock();
    bp.done.wait();
    t.join();
    return v;
}

const Tally = struct {
    wg: Thread.WaitGroup = .{},
    m: Thread.Mutex = .{},
    n: u32 = 0,
};

fn task(s: *Tally) void {
    defer s.wg.finish();
    s.m.lock();
    defer s.m.unlock();
    s.n += 1;
}

/// Two threads add 1 each and finish a `Thread.WaitGroup`; the main thread waits on it: 2.
pub fn waitGroup() !u32 {
    var s: Tally = .{};
    s.wg.startMany(2);
    const t1 = try Thread.spawn(.{}, task, .{&s});
    errdefer t1.join();
    const t2 = try Thread.spawn(.{}, task, .{&s});
    s.wg.wait();
    const n = s.n;
    t1.join();
    t2.join();
    return n;
}

comptime {
    _ = &mutexCounter;
    _ = &handoff;
    _ = &waitGroup;
}
