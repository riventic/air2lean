// B1 regression: a user `Thread.zig` must not bind to the std `Thread` model.
const Thread = @import("Thread.zig");

pub export fn entry(x: u32) u32 {
    return Thread.spawn(.{ .id = 7 }, x);
}
