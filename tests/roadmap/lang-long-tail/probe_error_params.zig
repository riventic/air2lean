//! Native probe of `error_params.zig` (stock Zig 0.14.1-0.17.0). Each line is
//! `<function> <input> <result>`: a value, `error.<Name>`, or `panic` (a safety check fired; the
//! probe runs each panicking case last). `Model.lean` prints the same lines from the translation.
const std = @import("std");
const ep = @import("error_params.zig");

fn print(comptime fmt: []const u8, args: anytype) void {
    std.debug.print(fmt, args);
}

fn eu(name: []const u8, input: u32, r: anyerror!u32) void {
    if (r) |v| print("{s} {d} {d}\n", .{ name, input, v }) else |e| print("{s} {d} error.{s}\n", .{ name, input, @errorName(e) });
}

pub fn main() void {
    const inputs = [_]u32{ 0, 1, 2, 7, 0x7fffffff };
    for (inputs) |x| eu("orBoom", x, ep.orBoom(x, error.Boom));
    for (inputs) |x| eu("forward", x, ep.forward(x));
    for (inputs) |x| print("viaFail {d} {d}\n", .{ x, ep.viaFail(x) });
    for (inputs) |x| print("unwrapEmpty {d} {d}\n", .{ x, ep.unwrapEmpty(x) });
    for (inputs) |x| print("skipFirst {d} {d}\n", .{ x, ep.skipFirst(error.Boom, x) });
}
