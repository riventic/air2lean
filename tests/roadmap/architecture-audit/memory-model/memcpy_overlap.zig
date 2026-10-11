// MM-15 control: `@memcpy` with overlapping ranges. ReleaseSafe AIR carries the alias check,
// so the model must panic like the native build.
const std = @import("std");

pub noinline fn memcpyOverlap(k: usize) u8 {
    var buf: [8]u8 = .{ 1, 2, 3, 4, 5, 6, 7, 8 };
    @memcpy(buf[k .. k + 4], buf[0..4]);
    return buf[4];
}

pub fn main() void {
    std.debug.print("memcpyOverlap4 {d}\n", .{memcpyOverlap(4)});
    std.debug.print("memcpyOverlap1 {d}\n", .{memcpyOverlap(1)});
}
