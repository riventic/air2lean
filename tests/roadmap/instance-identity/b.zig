// Program B: other instances first (so the compiler numbers its instances differently), then
// some of program A's (a.zig), with the same function names.
const std = @import("std");
const lib = @import("lib.zig");

pub fn scaleU16By7(x: u16) u16 {
    return lib.scale(u16, 7, x);
}
pub fn scaleI32By3(x: i32) i32 {
    return lib.scale(i32, 3, x);
}
pub fn prefixXyz(x: u32) u32 {
    return lib.prefixLen("xyz", x);
}
pub fn widenU32(x: u32) u64 {
    return lib.widen(x);
}
pub fn dupeWords(a: std.mem.Allocator, s: []const u32) ![]u32 {
    return a.dupe(u32, s);
}
pub fn scaleU32By3(x: u32) u32 {
    return lib.scale(u32, 3, x);
}
pub fn taggedSafe(x: u32) u32 {
    return lib.tagged(.safe, x);
}
pub fn prefixAb(x: u32) u32 {
    return lib.prefixLen("ab", x);
}
pub fn applyInc(x: u32) u32 {
    return lib.apply(lib.inc, x);
}
pub fn firstOf12(x: u32) u32 {
    return lib.first(.{ .a = 1, .b = 2 }, x);
}
pub fn boundedLimit(x: u32) u32 {
    return lib.bounded(&lib.limit, x);
}
pub fn widenU8(x: u8) u64 {
    return lib.widen(x);
}
pub fn dupeBytes(a: std.mem.Allocator, s: []const u8) ![]u8 {
    return a.dupe(u8, s);
}

comptime {
    _ = &scaleU16By7;
    _ = &scaleI32By3;
    _ = &prefixXyz;
    _ = &widenU32;
    _ = &dupeWords;
    _ = &scaleU32By3;
    _ = &taggedSafe;
    _ = &prefixAb;
    _ = &applyInc;
    _ = &firstOf12;
    _ = &boundedLimit;
    _ = &widenU8;
    _ = &dupeBytes;
}
