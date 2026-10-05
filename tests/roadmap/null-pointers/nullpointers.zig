const std = @import("std");

pub noinline fn cNull(address: usize) bool {
    const p: [*c]const u8 = @ptrFromInt(address);
    return p == null;
}
pub noinline fn allowzeroAddress(address: usize) usize {
    const p: *allowzero const u8 = @ptrFromInt(address);
    return @intFromPtr(p);
}
pub noinline fn allowzeroManyAddress(address: usize) usize {
    const p: [*]allowzero const u8 = @ptrFromInt(address);
    return @intFromPtr(p);
}
pub noinline fn castChecked(address: usize) bool {
    const p: [*c]const u8 = @ptrFromInt(address);
    if (p == null) return false;
    const q: *const u8 = @ptrCast(p);
    return @intFromPtr(q) == address;
}
pub noinline fn cRead(p: [*c]const u8) u8 {
    if (p == null) return 0;
    return p.*;
}
pub noinline fn cZero() [*c]const u8 { return null; }

pub fn main() void {
    for ([_]usize{ 0, 1, 8, 4095, 65535, std.math.maxInt(usize) }) |n| {
        std.debug.print("{d} {d} {d} {d} {d}\n", .{ n, @intFromBool(cNull(n)), allowzeroAddress(n), allowzeroManyAddress(n), @intFromBool(castChecked(n)) });
    }
    const byte: u8 = 37;
    std.debug.print("read {d} {d}\n", .{ cRead(null), cRead(@ptrCast(&byte)) });
    std.debug.print("zero {d}\n", .{@intFromPtr(cZero())});
}
