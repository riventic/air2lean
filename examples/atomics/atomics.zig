//! T2: the RC11 memory model of atomics (`docs/std-models.md` §Thread model). Each function
//! runs two threads that share atomics without a lock, and returns what the main thread saw.
//! A result that only a weak memory model explains is in the model's set of results.

const std = @import("std");
const Thread = std.Thread;
const A = std.atomic.Value(u32);

const MpCtx = struct {
    data: *u32,
    flag: *A,
};

fn mpWriter(c: *MpCtx) void {
    c.data.* = 42;
    c.flag.store(1, .release);
}

fn mpWriterRelaxed(c: *MpCtx) void {
    c.data.* = 42;
    c.flag.store(1, .monotonic);
}

/// Message passing: when the reader sees the flag (acquire), it sees the data. The result is 0
/// (the flag is not set yet) or 42, never a stale 0 after the flag.
pub fn mpRelAcq() !u32 {
    var data: u32 = 0;
    var flag = A.init(0);
    var c: MpCtx = .{ .data = &data, .flag = &flag };
    const h = try Thread.spawn(.{}, mpWriter, .{&c});
    const r = if (flag.load(.acquire) == 1) data else 0;
    h.join();
    return r;
}

/// The same with a `.monotonic` flag: no happens-before edge, so the read of the data after the
/// flag is a data race (`.illegal` in the model).
pub fn mpRelaxed() !u32 {
    var data: u32 = 0;
    var flag = A.init(0);
    var c: MpCtx = .{ .data = &data, .flag = &flag };
    const h = try Thread.spawn(.{}, mpWriterRelaxed, .{&c});
    const r = if (flag.load(.monotonic) == 1) data else 0;
    h.join();
    return r;
}

const SbCtx = struct {
    mine: *A,
    other: *A,
    out: *u32,
};

fn sb(c: *SbCtx) void {
    c.mine.store(1, .monotonic);
    c.out.* = c.other.load(.monotonic);
}

/// Store buffering with relaxed atomics: each thread writes its flag, then reads the other one.
/// `r1 | r2 << 1`; 0 (both read the old value) is a result of a weak memory model.
pub fn sbRelaxed() !u32 {
    var x = A.init(0);
    var y = A.init(0);
    var r1: u32 = 0;
    var r2: u32 = 0;
    var c1: SbCtx = .{ .mine = &x, .other = &y, .out = &r1 };
    var c2: SbCtx = .{ .mine = &y, .other = &x, .out = &r2 };
    const h1 = try Thread.spawn(.{}, sb, .{&c1});
    errdefer h1.join();
    const h2 = try Thread.spawn(.{}, sb, .{&c2});
    h1.join();
    h2.join();
    return r1 | (r2 << 1);
}

const WwCtx = struct {
    a: *A,
    b: *A,
};

fn ww(c: *WwCtx) void {
    c.a.store(1, .monotonic);
    c.b.store(2, .monotonic);
}

/// 2+2W: one thread writes `x = 1, y = 2`, the other `y = 1, x = 2`, all relaxed. The final
/// values `10 * x + y`; 11 (both first writes last) is a result of a weak memory model.
pub fn twoPlusTwoW() !u32 {
    var x = A.init(0);
    var y = A.init(0);
    var c1: WwCtx = .{ .a = &x, .b = &y };
    var c2: WwCtx = .{ .a = &y, .b = &x };
    const h1 = try Thread.spawn(.{}, ww, .{&c1});
    errdefer h1.join();
    const h2 = try Thread.spawn(.{}, ww, .{&c2});
    h1.join();
    h2.join();
    return 10 * x.load(.seq_cst) + y.load(.seq_cst);
}

const Stack = struct {
    /// The top node, `0` for none (nodes are `1` and `2`).
    head: A,
    /// `next[i]`: the node under node `i`.
    next: [3]u32,
};

const PushCtx = struct {
    s: *Stack,
    node: u32,
};

fn push(c: *PushCtx) void {
    var h = c.s.head.load(.monotonic);
    while (true) {
        c.s.next[c.node] = h;
        h = c.s.head.cmpxchgWeak(h, c.node, .release, .monotonic) orelse break;
    }
}

/// A lock-free stack: two threads push node 1 and node 2 with `cmpxchgWeak`. Both nodes are on
/// the stack: the result is `12` or `21` (top first) then `0`, as `100 * top + 10 * under`.
pub fn stackPush() !u32 {
    var s: Stack = .{ .head = A.init(0), .next = .{ 0, 0, 0 } };
    var c1: PushCtx = .{ .s = &s, .node = 1 };
    var c2: PushCtx = .{ .s = &s, .node = 2 };
    const h1 = try Thread.spawn(.{}, push, .{&c1});
    errdefer h1.join();
    const h2 = try Thread.spawn(.{}, push, .{&c2});
    h1.join();
    h2.join();
    const top = s.head.load(.acquire);
    return 100 * top + 10 * s.next[top] + s.next[s.next[top]];
}

comptime {
    _ = &mpRelAcq;
    _ = &mpRelaxed;
    _ = &sbRelaxed;
    _ = &twoPlusTwoW;
    _ = &stackPush;
}
