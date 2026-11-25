//! Native reference for Eval.lean: the defined cases of `abi.c`'s entry points (`abi.zig`),
//! compiled by stock Zig 0.17.1 with `-lc -target x86_64-linux-musl` (Zig's libc, whose
//! definitions the model binds) and run on x86_64-linux. The illegal cases are not run.
const std = @import("std");
const p = @import("abi.zig");

pub fn main() void {
    std.debug.print("cmp_case {d} {d} {d}\n", .{ p.cmp_case(0), p.cmp_case(1), p.cmp_case(2) });
    std.debug.print("last_case {d} {d} {d} {d}\n", .{
        p.last_case(0, ','), p.last_case(0, 'z'), p.last_case(1, 'a'), p.last_case(0, 0),
    });
    std.debug.print("rfind_case {d}\n", .{p.rfind_case(0)});
    std.debug.print("usable_case {d} {d}\n", .{ p.usable_case(0, 7), p.usable_case(1, 100) });
}
