//! Native probe of `float_lanes.zig` (stock Zig 0.14.1-0.16.0). Floats print as their bits.
//! `ModelFloatLanes.lean` prints the same lines from the translation.
const std = @import("std");
const fl = @import("float_lanes.zig");

fn rt(x: f80) f80 {
    var s = x;
    const p: *volatile f80 = &s;
    return p.*;
}

pub fn main() void {
    var v: @Vector(2, f80) = .{ rt(1.5), rt(-2.25) };
    fl.swap(&v);
    std.debug.print("swap {x} {x}\n", .{ @as(u80, @bitCast(v[0])), @as(u80, @bitCast(v[1])) });
    for ([_]f80{ 0.0, 10.0, -7.5 }) |x| {
        std.debug.print("middle {x} {x}\n", .{ @as(u80, @bitCast(x)), @as(u80, @bitCast(fl.middle(rt(x)))) });
    }
}
