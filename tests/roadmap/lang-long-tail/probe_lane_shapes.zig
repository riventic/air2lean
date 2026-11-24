//! Native probe of `lane_shapes.zig` (stock Zig 0.14.1-0.17.1). `ModelLaneShapes.lean` prints
//! the same lines from the translation. `globalLane` writes the global, so it runs once.
const std = @import("std");
const ls = @import("lane_shapes.zig");

fn rt(comptime T: type, x: T) T {
    var s = x;
    const p: *volatile T = &s;
    return p.*;
}

pub fn main() void {
    std.debug.print("globalLane {x} {x}\n", .{ 0x1aa, ls.globalLane(rt(u16, 0x1aa)) });
    for ([_]u32{ 0, 0x89abcdef, 0xffffffff }) |a| {
        for ([_]u16{ 0, 0x155, 0xfe01 }) |x| {
            std.debug.print("viaResult {x} {x} {x}\n", .{ a, x, ls.viaResult(rt(u32, a), rt(u16, x)) });
            std.debug.print("viaField {x} {x} {x}\n", .{ a, x, ls.viaField(rt(u32, a), rt(u16, x)) });
            std.debug.print("fieldLane {x} {x} {x}\n", .{ a, x, ls.fieldLane(rt(u32, a), rt(u16, x)) });
            std.debug.print("byteLocal {x} {x} {x}\n", .{ a, x, ls.byteLocal(rt(u32, a), rt(u32, x)) });
        }
        std.debug.print("constLane {x} {x}\n", .{ a, ls.constLane(rt(u32, a)) });
    }
}
