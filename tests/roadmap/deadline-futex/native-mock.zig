//! Deterministic public-Io callback fixture; not OS clock/futex conformance.
const std = @import("std");
const probe = @import("probe");
const Io = std.Io;

const Reason = enum { mismatch, timeout, wake };
const Env = struct {
    time: i96 = 10,
    observations: usize = 0,
    waits: usize = 0,
    wake_at_boundary: bool = false,
    reason: Reason = .mismatch,
};

fn environment(userdata: ?*anyopaque) *Env {
    return @ptrCast(@alignCast(userdata.?));
}

fn now(userdata: ?*anyopaque, clock: Io.Clock) Io.Timestamp {
    std.debug.assert(clock == .awake);
    const env = environment(userdata);
    env.observations += 1;
    return .{ .nanoseconds = env.time };
}

fn wait(userdata: ?*anyopaque, ptr: *const u32, expected: u32, timeout: Io.Timeout) Io.Cancelable!void {
    const env = environment(userdata);
    env.waits += 1;
    if (ptr.* != expected) {
        env.reason = .mismatch;
        return;
    }
    switch (timeout) {
        .none => unreachable, // this fixture never requests an unbounded wait
        .duration => |duration| {
            std.debug.assert(duration.clock == .awake);
            std.debug.assert(duration.raw.nanoseconds == 0);
            env.reason = .timeout;
        },
        .deadline => |deadline| {
            std.debug.assert(deadline.clock == .awake);
            env.reason = if (env.time < deadline.raw.nanoseconds or
                (env.time == deadline.raw.nanoseconds and env.wake_at_boundary)) .wake else .timeout;
        },
    }
}

pub fn main() !void {
    // Static call closure: observe -> Io.Clock.now -> vtable.now;
    // waitZero/waitDeadline -> Io.futexWaitTimeout -> vtable.futexWait.
    // boundaryClient composes only those calls and stack scalar operations.
    // No Io lifecycle/deinit, allocation, printing, sleep or Threaded operation is called.
    var vtable: Io.VTable = undefined;
    vtable.now = now;
    vtable.futexWait = wait;
    var env: Env = .{};
    const io: Io = .{ .userdata = &env, .vtable = &vtable };
    const word: u32 = 0;
    try probe.waitZero(io, &word, 1);
    std.debug.assert(env.reason == .mismatch);
    try probe.waitZero(io, &word, 0);
    std.debug.assert(env.reason == .timeout);
    const first = probe.observe(io);
    const second = probe.observe(io);
    std.debug.assert(first == 10 and second == first);
    try probe.waitDeadline(io, &word, 0, 11);
    std.debug.assert(env.reason == .wake);
    try probe.waitDeadline(io, &word, 0, 10);
    std.debug.assert(env.reason == .timeout);
    env.wake_at_boundary = true;
    try probe.waitDeadline(io, &word, 0, 10);
    std.debug.assert(env.reason == .wake);
    env.wake_at_boundary = false;
    std.debug.assert(try probe.boundaryClient(io) == 73);
    std.debug.assert(env.reason == .timeout and env.waits == 6 and env.observations == 3);
}
