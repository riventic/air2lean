const std = @import("std");

pub fn makeZero(a: std.mem.Allocator, n: usize) ![:0]u8 {
    return a.allocSentinel(u8, n, 0);
}
pub fn makeByte(a: std.mem.Allocator, n: usize) ![:42]u8 {
    return a.allocSentinel(u8, n, 42);
}
pub fn releaseZero(a: std.mem.Allocator, s: [:0]u8) void { a.free(s); }
pub fn releaseByte(a: std.mem.Allocator, s: [:42]u8) void { a.free(s); }
comptime { _ = &makeZero; _ = &makeByte; _ = &releaseZero; _ = &releaseByte; }
