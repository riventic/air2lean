//! Prints each case of `concurrency.zig` as `name: value` (decimal) on stderr, in the order of
//! `ConcDiff.lean`; `futexNoSleep` (Zig 0.14.1 and 0.15.2 only) last, as `ConcFutex.lean` prints it.
const std = @import("std");
const c = @import("concurrency.zig");

pub fn main() !void {
    const p = std.debug.print;
    p("storeThenBytes: {d}\n", .{c.storeThenBytes(0x0102_0304)});
    p("bytesThenLoad: {d}\n", .{c.bytesThenLoad(1, 2, 3, 4)});
    p("rmwCarryByte0: {d}\n", .{c.rmwCarryByte0(0x00FF, 0x0001)});
    p("casSwap: {d}\n", .{c.casSwap(0x0102_0304_0506_0708, 0x1112_1314_1516_1718)});
    p("rmwMax: {d}\n", .{c.rmwMax(-5, 3)});
    p("threadsAdd: {d}\n", .{try c.threadsAdd(3)});
    p("heapWord: {d}\n", .{try c.heapWord(std.heap.page_allocator, 0x0A0B_0C0D)});
    if (c.has_futex) p("futexNoSleep: {d}\n", .{c.futexNoSleep()});
}
