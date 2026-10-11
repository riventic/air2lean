//! Architecture audit (concurrency): model-side litmus fixtures. Each function is exported to
//! AIR, translated, and every schedule of the model is enumerated by Enumerate.lean, which
//! prints the set of outcomes. native_litmus.zig / native_io.zig are the native counterparts.

const std = @import("std");
const Thread = std.Thread;
const Io = std.Io;
const A = std.atomic.Value(u32);

// ---- LB: load buffering with .monotonic ---------------------------------------------------
const Lb = struct { x: *A, y: *A, r: *u32 };

fn lbOther(c: *Lb) void {
    c.r.* = c.y.load(.monotonic);
    c.x.store(1, .monotonic);
}

/// `r1 * 2 + r2`. RC11 (and the Arm architecture) allow 3; the model has no promises, so it
/// never produces 3 (documented trusted assumption "no load buffering").
pub fn lbRelaxed() !u32 {
    var x = A.init(0);
    var y = A.init(0);
    var r2: u32 = 0;
    var c: Lb = .{ .x = &x, .y = &y, .r = &r2 };
    const h = try Thread.spawn(.{}, lbOther, .{&c});
    const r1 = x.load(.monotonic);
    y.store(1, .monotonic);
    h.join();
    return r1 * 2 + r2;
}

// ---- MP with relaxed atomics only (sanity: the model must allow the stale read) ------------
const Mp = struct { data: *A, flag: *A };

fn mpWriter(c: *Mp) void {
    c.data.store(42, .monotonic);
    c.flag.store(1, .monotonic);
}

/// `flag * 100 + data`: 100 (flag seen, data stale) is observed natively on aarch64.
pub fn mpAllRelaxed() !u32 {
    var data = A.init(0);
    var flag = A.init(0);
    var c: Mp = .{ .data = &data, .flag = &flag };
    const h = try Thread.spawn(.{}, mpWriter, .{&c});
    const f = flag.load(.monotonic);
    const d = data.load(.monotonic);
    h.join();
    return f * 100 + d;
}

// ---- futex: does the waiter only return after a wake? -----------------------------------
const Fw = struct { io: Io, w: *A, after: *A };

fn fwWaiter(c: *Fw) void {
    c.io.futexWaitUncancelable(u32, &c.w.raw, 0);
    c.after.store(1, .release);
}

/// 1 iff the waiter got past its futex wait before the caller changed the word or woke it.
/// Without spurious wakeups (origin/main) the model only produces 0; std documents spurious
/// returns and native_io.zig observes one (EINTR), so the native result 1 is possible.
pub fn futexEarly(io: Io) !u32 {
    var w = A.init(0);
    var after = A.init(0);
    var c: Fw = .{ .io = io, .w = &w, .after = &after };
    const h = try Thread.spawn(.{}, fwWaiter, .{&c});
    const r = after.load(.acquire);
    w.store(1, .release);
    io.futexWake(u32, &w.raw, 1);
    h.join();
    return r;
}

// ---- Io.Group.async that waits for the caller ----------------------------------------------
const Gt = struct { io: Io, gate: *A };

fn gated(c: *Gt) void {
    while (c.gate.load(.acquire) == 0) c.io.futexWaitUncancelable(u32, &c.gate.raw, 0);
}

/// Two group tasks wait for a gate that the caller opens after `async`. The model (available
/// policy) spawns a thread per task, so the call returns 7. std's Io.Threaded runs a task in
/// the caller once `async_limit` (cpu count - 1; 0 single-threaded) is reached: deadlock.
pub fn groupGate(io: Io) !u32 {
    var gate = A.init(0);
    var c: Gt = .{ .io = io, .gate = &gate };
    var g: Io.Group = .init;
    g.async(io, gated, .{&c});
    g.async(io, gated, .{&c});
    gate.store(1, .release);
    io.futexWake(u32, &gate.raw, std.math.maxInt(u32));
    try g.await(io);
    return 7;
}

// ---- stack lifetime end is not an access -------------------------------------------------
const Sl = struct { x: *u32, done: *A, out: *u32 };

fn slReader(c: *Sl) void {
    c.out.* = c.x.*;
    c.done.store(1, .monotonic);
}

fn slHelper(done: *A, out: *u32) !Thread {
    var x: u32 = 5;
    var c: Sl = .{ .x = &x, .done = done, .out = out };
    const h = try Thread.spawn(.{}, slReader, .{&c});
    // Relaxed handshake: no happens-before from the reader's load of `x` to the frame's end.
    while (done.load(.monotonic) == 0) {}
    return h;
}

fn touch(p: *u32) void {
    p.* +%= 0;
}

/// A new frame whose escaping local can reuse the helper's dead stack slot.
fn clobber(v: u32) u32 {
    var s: u32 = v;
    touch(&s);
    return s;
}

/// The reader's plain load of the helper's local races with the frame's end and the reuse
/// of its stack slot (no happens-before: the handshake is relaxed). The model records no
/// access at a stack frame's end, so no schedule reports the race: it returns 5 + 9.
pub fn stackLifetime() !u32 {
    var done = A.init(0);
    var out: u32 = 0;
    const h = try slHelper(&done, &out);
    const z = clobber(9);
    h.join();
    return out + z;
}

comptime {
    _ = &lbRelaxed;
    _ = &mpAllRelaxed;
    _ = &futexEarly;
    _ = &groupGate;
    _ = &stackLifetime;
}
