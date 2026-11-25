//! Native probe of `lane_values.zig` (stock Zig 0.14.1-0.17.1). `ModelLaneValues.lean` prints
//! the same lines from the translation. The `global*` functions write a global, so each runs once.
const std = @import("std");
const lv = @import("lane_values.zig");

fn rt(comptime T: type, x: T) T {
    var s = x;
    const p: *volatile T = &s;
    return p.*;
}

pub fn main() void {
    std.debug.print("globalU8 {x}\n", .{lv.globalU8(rt(u32, 0x5a))});
    std.debug.print("globalU32 {x}\n", .{lv.globalU32(rt(u32, 0x5a))});
    std.debug.print("globalU128 {x}\n", .{lv.globalU128(rt(u32, 0x5a))});
    std.debug.print("globalF64 {x}\n", .{lv.globalF64(rt(u32, 0x5a))});
    for ([_]u32{ 0, 0x89abcdef, 0xffffffff }) |a| {
        for ([_]u32{ 0, 0x1234567 }) |x| {
            std.debug.print("valuesU8 {x} {x} {x}\n", .{ a, x, lv.valuesU8(rt(u32, a), rt(u32, x)) });
            std.debug.print("valuesI16 {x} {x} {x}\n", .{ a, x, lv.valuesI16(rt(u32, a), rt(u32, x)) });
            std.debug.print("valuesU32 {x} {x} {x}\n", .{ a, x, lv.valuesU32(rt(u32, a), rt(u32, x)) });
            std.debug.print("valuesU64 {x} {x} {x}\n", .{ a, x, lv.valuesU64(rt(u32, a), rt(u32, x)) });
            std.debug.print("valuesU128 {x} {x} {x}\n", .{ a, x, lv.valuesU128(rt(u32, a), rt(u32, x)) });
            std.debug.print("valuesF32 {x} {x} {x}\n", .{ a, x, lv.valuesF32(rt(u32, a), rt(u32, x)) });
            std.debug.print("valuesF64 {x} {x} {x}\n", .{ a, x, lv.valuesF64(rt(u32, a), rt(u32, x)) });
        }
        std.debug.print("offset {x} {d} {d} {d}\n", .{ a, lv.offsetU8(rt(u32, a)), lv.offsetU32(rt(u32, a)), lv.offsetF64(rt(u32, a)) });
    }
}
