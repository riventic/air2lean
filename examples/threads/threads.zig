//! M22: atomics and fork-join threads (`docs/std-models.md` §Thread model). Fork-join only:
//! `std.Thread.spawn`/`.join`. No `Mutex`, `Condition`, `Futex`, `.detach`, `.yield`,
//! `.spinLoopHint` — outside this subset (`Air2Lean.Memory.lean`'s `rejectedThreadFn?`).

const std = @import("std");
const Thread = std.Thread;

/// One thread's share of the counter work.
const CounterCtx = struct {
    counter: *std.atomic.Value(u32),
    n: u32,
};

fn bump(ctx: *CounterCtx) void {
    var i: u32 = 0;
    while (i < ctx.n) : (i += 1) {
        _ = ctx.counter.fetchAdd(1, .seq_cst);
    }
}

/// 4 threads each increment a shared atomic counter `itersPerThread` times. The result is
/// always `4 * itersPerThread`, regardless of interleaving: `fetchAdd` is atomic.
pub fn parallelCounter(itersPerThread: u32) !u32 {
    var counter = std.atomic.Value(u32).init(0);
    var ctxs: [4]CounterCtx = undefined;
    for (&ctxs) |*c| c.* = .{ .counter = &counter, .n = itersPerThread };
    var handles: [4]Thread = undefined;
    for (&handles, &ctxs) |*h, *c| h.* = try Thread.spawn(.{}, bump, .{c});
    for (&handles) |*h| h.join();
    return counter.load(.seq_cst);
}

/// One thread's racing write.
const RaceCtx = struct {
    flag: *u32,
    val: u32,
};

fn writeFlag(ctx: *RaceCtx) void {
    ctx.flag.* = ctx.val;
}

/// Two threads write the same `u32` without synchronization: a data race. The model rejects
/// every call (`.illegal`, `docs/std-models.md` §Thread model); real Zig performs the racing
/// writes with an OS-scheduler-dependent outcome (`tests/diff/threads/unspecified.txt`).
pub fn race(a: u32, b: u32) !u32 {
    var flag: u32 = 0;
    var c1: RaceCtx = .{ .flag = &flag, .val = a };
    var c2: RaceCtx = .{ .flag = &flag, .val = b };
    const h1 = try Thread.spawn(.{}, writeFlag, .{&c1});
    const h2 = try Thread.spawn(.{}, writeFlag, .{&c2});
    h1.join();
    h2.join();
    return flag;
}

/// Two threads each write their own `u32` (`writeFlag`, as in `race`, but two locations): no
/// data race. The result is always `a +% b`.
pub fn disjoint(a: u32, b: u32) !u32 {
    var x: u32 = 0;
    var y: u32 = 0;
    var c1: RaceCtx = .{ .flag = &x, .val = a };
    var c2: RaceCtx = .{ .flag = &y, .val = b };
    const h1 = try Thread.spawn(.{}, writeFlag, .{&c1});
    const h2 = try Thread.spawn(.{}, writeFlag, .{&c2});
    h1.join();
    h2.join();
    return x +% y;
}

/// One thread's racing atomic swap.
const SwapCtx = struct {
    flag: *std.atomic.Value(u32),
    val: u32,
};

fn swapFlag(ctx: *SwapCtx) void {
    _ = ctx.flag.swap(ctx.val, .seq_cst);
}

/// Two threads swap the same atomic `u32` without an ordering between them: `Xchg` never
/// The two swaps are atomic, so they do not race: the result is `a` or `b`, by the schedule
/// (`docs/std-models.md` §Thread model); the diff test searches the schedules for the result
/// that real Zig gave (`tests/diff/Diff.lean`'s `searchSchedules`).
pub fn xchgRace(a: u32, b: u32) !u32 {
    var flag = std.atomic.Value(u32).init(0);
    var c1: SwapCtx = .{ .flag = &flag, .val = a };
    var c2: SwapCtx = .{ .flag = &flag, .val = b };
    const h1 = try Thread.spawn(.{}, swapFlag, .{&c1});
    const h2 = try Thread.spawn(.{}, swapFlag, .{&c2});
    h1.join();
    h2.join();
    return flag.load(.seq_cst);
}

/// A claim on a job: `idle` until one thread takes it.
const Phase = enum(u32) { idle, busy, done };

const ClaimCtx = struct {
    phase: *std.atomic.Value(Phase),
    wins: *std.atomic.Value(u32),
};

fn claim(ctx: *ClaimCtx) void {
    if (ctx.phase.cmpxchgStrong(.idle, .busy, .acq_rel, .acquire) == null) {
        _ = ctx.wins.fetchAdd(1, .monotonic);
    }
}

/// Two threads try to claim one job (an atomic `cmpxchg` on an enum): exactly one wins, so the
/// result is always `1 + @intFromEnum(.busy)` = 2.
pub fn claimOnce() !u32 {
    var phase = std.atomic.Value(Phase).init(.idle);
    var wins = std.atomic.Value(u32).init(0);
    var ctx: ClaimCtx = .{ .phase = &phase, .wins = &wins };
    const h1 = try Thread.spawn(.{}, claim, .{&ctx});
    const h2 = try Thread.spawn(.{}, claim, .{&ctx});
    h1.join();
    h2.join();
    return wins.load(.seq_cst) + @intFromEnum(phase.load(.seq_cst));
}

comptime {
    _ = &parallelCounter;
    _ = &race;
    _ = &disjoint;
    _ = &xchgRace;
    _ = &claimOnce;
}
