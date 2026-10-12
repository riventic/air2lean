//! Native probe of `runtime_lanes.zig` (stock Zig 0.14.1 and 0.15.2). For each vector and each
//! lane: the lanes after a store at that runtime index (floats by their bits). `fillSum` for
//! n = 0..5. `ModelRuntimeLanes.lean` prints the same lines from the translation.
const std = @import("std");
const rl = @import("runtime_lanes.zig");

fn rt(comptime T: type, x: T) T {
    var s = x;
    const p: *volatile T = &s;
    return p.*;
}

fn show(comptime name: []const u8, comptime N: usize, comptime T: type, v: @Vector(N, T), i: usize) void {
    std.debug.print("{s} {d}", .{ name, i });
    inline for (0..N) |k| {
        const lane = v[k];
        if (T == f80) std.debug.print(" {x}", .{@as(u80, @bitCast(lane))}) else if (T == bool) std.debug.print(" {d}", .{@intFromBool(lane)}) else std.debug.print(" {d}", .{lane});
    }
    std.debug.print("\n", .{});
}

pub fn main() void {
    for (0..4) |i| {
        var v: @Vector(4, u9) = .{ 1, 2, 3, 4 };
        rl.setU9(&v, rt(usize, i), rt(u9, 500));
        show("setU9", 4, u9, v, i);
    }
    for (0..3) |i| {
        var v: @Vector(3, u24) = .{ 0x10, 0x20, 0x30 };
        rl.setU24(&v, rt(usize, i), rt(u24, 0xabcdef));
        show("setU24", 3, u24, v, i);
    }
    for (0..5) |i| {
        var v: @Vector(5, bool) = .{ true, false, true, false, true };
        rl.setBool(&v, rt(usize, i), rt(bool, i % 2 == 1));
        show("setBool", 5, bool, v, i);
    }
    for (0..2) |i| {
        var v: @Vector(2, f80) = .{ 1.5, -2.25 };
        rl.setF80(&v, rt(usize, i), rt(f80, 3.0));
        show("setF80", 2, f80, v, i);
    }
    for (0..6) |n| std.debug.print("fillSum {d} {d}\n", .{ n, rl.fillSum(rt(usize, n)) });
}
