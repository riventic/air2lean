//! Source preparation only; ROOT must export actual AIR before model implementation.
const std = @import("std");
const Io = std.Io;

pub fn observe(io: Io) i96 {
    return Io.Clock.awake.now(io).nanoseconds;
}

pub fn waitZero(io: Io, word: *const u32, expected: u32) Io.Cancelable!void {
    try io.futexWaitTimeout(u32, word, expected, .{
        .duration = .{ .raw = .zero, .clock = .awake },
    });
}

pub fn waitDeadline(io: Io, word: *const u32, expected: u32, deadline: i96) Io.Cancelable!void {
    try io.futexWaitTimeout(u32, word, expected, .{
        .deadline = .{ .raw = .{ .nanoseconds = deadline }, .clock = .awake },
    });
}

pub fn boundaryClient(io: Io) Io.Cancelable!u32 {
    const word: u32 = 0;
    const sentinel: u32 = 73;
    const deadline = observe(io);
    try waitDeadline(io, &word, 0, deadline);
    // Successful return says neither "woken" nor "timed out". No other writer exists.
    return word + sentinel;
}

comptime {
    _ = &observe;
    _ = &waitZero;
    _ = &waitDeadline;
    _ = &boundaryClient;
}
