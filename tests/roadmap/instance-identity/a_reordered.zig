// Program A in the opposite source and reference order (a.zig).
const std = @import("std");
const lib = @import("lib.zig");

comptime {
    _ = &dupeBytes;
    _ = &widenU16;
    _ = &widenU8;
    _ = &boundedLimit;
    _ = &firstOf13;
    _ = &firstOf12;
    _ = &applyDec;
    _ = &applyInc;
    _ = &prefixAbc;
    _ = &prefixAb;
    _ = &taggedSafe;
    _ = &taggedFast;
    _ = &scaleUsizeBy3;
    _ = &scaleU8By3;
    _ = &scaleU32By5;
    _ = &scaleU32By3;
}

pub fn dupeBytes(a: std.mem.Allocator, s: []const u8) ![]u8 {
    return a.dupe(u8, s);
}
pub fn widenU16(x: u16) u64 {
    return lib.widen(x);
}
pub fn widenU8(x: u8) u64 {
    return lib.widen(x);
}
pub fn boundedLimit(x: u32) u32 {
    return lib.bounded(&lib.limit, x);
}
pub fn firstOf13(x: u32) u32 {
    return lib.first(.{ .a = 1, .b = 3 }, x);
}
pub fn firstOf12(x: u32) u32 {
    return lib.first(.{ .a = 1, .b = 2 }, x);
}
pub fn applyDec(x: u32) u32 {
    return lib.apply(lib.dec, x);
}
pub fn applyInc(x: u32) u32 {
    return lib.apply(lib.inc, x);
}
pub fn prefixAbc(x: u32) u32 {
    return lib.prefixLen("abc", x);
}
pub fn prefixAb(x: u32) u32 {
    return lib.prefixLen("ab", x);
}
pub fn taggedSafe(x: u32) u32 {
    return lib.tagged(.safe, x);
}
pub fn taggedFast(x: u32) u32 {
    return lib.tagged(.fast, x);
}
pub fn scaleUsizeBy3(x: usize) usize {
    return lib.scale(usize, 3, x);
}
pub fn scaleU8By3(x: u8) u8 {
    return lib.scale(u8, 3, x);
}
pub fn scaleU32By5(x: u32) u32 {
    return lib.scale(u32, 5, x);
}
pub fn scaleU32By3(x: u32) u32 {
    return lib.scale(u32, 3, x);
}
