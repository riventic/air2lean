//! Native results of the defined exports of `ptrcasts.zig` on Q01's inputs, one
//! `name a b result` line each (`native.txt`; `Runtime.lean` checks the model against it).
const std = @import("std");
const p = @import("ptrcasts.zig");

const inputs = [_][2]u32{ .{ 0, 0 }, .{ 1, 2 }, .{ 4294967295, 7 }, .{ 305419896, 2863311530 } };
const fns = .{
    .{ "listSum", p.listSum },
    .{ "treeInsert", p.treeInsert },
    .{ "voidRoundTrip", p.voidRoundTrip },
    .{ "byteView", p.byteView },
    .{ "opaqueContext", p.opaqueContext },
};

pub fn main() void {
    inline for (fns) |f| {
        for (inputs) |in| std.debug.print("{s} {d} {d} {d}\n", .{ f[0], in[0], in[1], f[1](in[0], in[1]) });
    }
}
