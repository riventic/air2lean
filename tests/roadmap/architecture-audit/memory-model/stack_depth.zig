// MM-5: the model has no stack bound. `depth(n)` returns `n` in the model for every `n`;
// natively, ReleaseSafe overflows the main-thread stack and the process dies on a signal for
// large `n`.
const std = @import("std");

pub noinline fn depth(n: u64) u64 {
    var slot: [64]u8 = undefined;
    const p: [*]u8 = &slot;
    p[0] = @truncate(n);
    if (n == 0) return 0;
    return depth(n - 1) + 1 + (p[0] -% @as(u8, @truncate(n)));
}

pub fn main() void {
    std.debug.print("depth(1000) {d}\n", .{depth(1000)});
    std.debug.print("depth(10000000) {d}\n", .{depth(10_000_000)});
}
