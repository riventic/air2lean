//! Native reference for Eval.lean: the same exported entry points, compiled and run by stock
//! Zig. The extern calls link to libc_ref.zig's definitions.
const std = @import("std");
const p = @import("extern_calls.zig");

pub fn main() void {
    std.debug.print("fillSum {d} {d} {d} {d} {d}\n", .{
        p.fillSum(0, 7), p.fillSum(4, 0), p.fillSum(16, 255), p.fillSum(20, -1), p.fillSum(3, 258),
    });
    std.debug.print("greetLen {d} {d}\n", .{ p.greetLen(0), p.greetLen(1) });
}
