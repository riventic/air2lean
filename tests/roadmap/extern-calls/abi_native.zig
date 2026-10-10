//! Native reference for AbiEval.lean: abi_calls.zig's entry points with defined behaviour,
//! compiled and run by stock Zig. The extern calls link to abi_ref.zig's `@export`s.
const std = @import("std");
const p = @import("abi_calls.zig");

pub fn main() void {
    std.debug.print("fillSum {d} {d} {d} {d}\n", .{ p.fillSum(0, 7), p.fillSum(4, 0), p.fillSum(16, 255), p.fillSum(3, 2) });
    std.debug.print("lenOf {d} {d}\n", .{ p.lenOf(0), p.lenOf(1) });
    std.debug.print("firstAt {d} {d} {d}\n", .{ p.firstAt(0), p.firstAt(16), p.firstAt(40) });
}
