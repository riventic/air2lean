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

/// One thread's racing atomic swap.
const SwapCtx = struct {
    flag: *std.atomic.Value(u32),
    val: u32,
};

fn swapFlag(ctx: *SwapCtx) void {
    _ = ctx.flag.swap(ctx.val, .seq_cst);
}

/// Two threads swap the same atomic `u32` without an ordering between them: `Xchg` never
/// commutes with itself (`ZigLean/Mem/Thread.lean`'s `RmwOp.group`), so the model always throws
/// `Zig.Error.nondet` (`docs/std-models.md` §Thread model); real Zig performs both swaps with an
/// OS-scheduler-dependent outcome (`tests/diff/threads/nondet.txt`).
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

comptime {
    _ = &parallelCounter;
    _ = &race;
    _ = &xchgRace;
}
