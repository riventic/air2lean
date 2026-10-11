//! Architecture audit (concurrency): native behaviour of the std.Io (0.16.0) futex and Group
//! primitives that the model hand-writes (ZigLean/Conc/Call.lean, ZigLean/Mem/Thread.lean).
//! Build: zig build-exe -OReleaseSafe native_io.zig; run: ./native_io
//!   1. spurious: an Io.futexWaitUncancelable returns without any futexWake (EINTR); the
//!      model has no spurious wakeup, so it proves the waiter always sees the woken value.
//!   2. order: which of three waiters (that began waiting in order A, B, C) a wake(1) wakes;
//!      the model always wakes the first (FIFO, Thread.futexWake).
//!   3. group: Io.Group.async past the Threaded async_limit runs the task eagerly in the
//!      caller; a task that waits for the caller then deadlocks. The model spawns a thread.
const std = @import("std");
const Io = std.Io;

fn ms(io: Io, n: i64) void {
    io.sleep(.fromMilliseconds(n), .awake) catch {};
}

// ---- 1. spurious wakeup -------------------------------------------------------------------
var word = std.atomic.Value(u32).init(0);
var seen = std.atomic.Value(u32).init(99);

fn onSignal(_: std.c.SIG) callconv(.c) void {}

fn waiter(io: Io) void {
    io.futexWaitUncancelable(u32, &word.raw, 0);
    seen.store(word.load(.acquire), .release);
}

fn spurious(io: Io) !void {
    var act: std.c.Sigaction = .{
        .handler = .{ .handler = onSignal },
        .mask = std.posix.sigemptyset(),
        .flags = 0, // no SA_RESTART
    };
    std.posix.sigaction(.USR1, &act, null);
    word.store(0, .release);
    seen.store(99, .release);
    const t = try std.Thread.spawn(.{}, waiter, .{io});
    ms(io, 100);
    _ = std.c.pthread_kill(t.getHandle(), .USR1);
    ms(io, 100);
    const early = seen.load(.acquire);
    word.store(1, .release);
    io.futexWake(u32, &word.raw, 1);
    t.join();
    std.debug.print("spurious: waiter returned before any wake with value {d} (model: impossible; 99 = still waiting)\n", .{early});
}

// ---- 2. wake order -------------------------------------------------------------------------
var word2 = std.atomic.Value(u32).init(0);
var first = std.atomic.Value(u32).init(0);

fn orderedWaiter(io: Io, id: u32) void {
    while (word2.load(.acquire) == 0) io.futexWaitUncancelable(u32, &word2.raw, 0);
    _ = first.cmpxchgStrong(0, id, .acq_rel, .acquire);
}

fn order(io: Io) !void {
    var counts = [_]u32{ 0, 0, 0, 0 };
    for (0..20) |_| {
        word2.store(0, .release);
        first.store(0, .release);
        var ts: [3]std.Thread = undefined;
        for (&ts, 1..) |*t, id| {
            t.* = try std.Thread.spawn(.{}, orderedWaiter, .{ io, @as(u32, @intCast(id)) });
            ms(io, 20); // waiter id is asleep before the next one starts
        }
        word2.store(1, .release);
        io.futexWake(u32, &word2.raw, 1);
        ms(io, 50);
        counts[first.load(.acquire)] += 1;
        io.futexWake(u32, &word2.raw, std.math.maxInt(u32));
        for (ts) |t| t.join();
    }
    std.debug.print("order: first woken A={d} B={d} C={d} (model: always A)\n", .{ counts[1], counts[2], counts[3] });
}

// ---- 3. Group.async run eagerly ------------------------------------------------------------
var gate = std.atomic.Value(u32).init(0);
var started = std.atomic.Value(u32).init(0);

fn task(io: Io) void {
    _ = started.fetchAdd(1, .acq_rel);
    while (gate.load(.acquire) == 0) io.futexWaitUncancelable(u32, &gate.raw, 0);
}

fn watchdog(io: Io) void {
    ms(io, 2000);
    std.debug.print("group: DEADLOCK - {d} tasks started, caller never reached gate.store (model: returns)\n", .{started.load(.acquire)});
    std.process.exit(0);
}

fn group(io: Io, n: usize) !void {
    const w = try std.Thread.spawn(.{}, watchdog, .{io});
    w.detach();
    var g: Io.Group = .init;
    for (0..n) |_| g.async(io, task, .{io});
    gate.store(1, .release);
    io.futexWake(u32, &gate.raw, std.math.maxInt(u32));
    try g.await(io);
    std.debug.print("group: completed\n", .{});
}

pub fn main() !void {
    var threaded: Io.Threaded = .init(std.heap.smp_allocator, .{});
    defer threaded.deinit();
    const io = threaded.io();
    try spurious(io);
    try order(io);
    const cpus = try std.Thread.getCpuCount();
    std.debug.print("group: {d} cpus, async_limit default = cpus - 1, spawning {d} tasks\n", .{ cpus, cpus });
    try group(io, cpus);
}
