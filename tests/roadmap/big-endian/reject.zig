//! T03: s390x-linux operations outside the qualified big-endian model. Each function's export
//! must be rejected by the translator (`test_cli.py`).
const std = @import("std");

pub fn atomicRead(p: *u32) u32 {
    return @atomicLoad(u32, p, .seq_cst);
}

pub const PU = packed union { a: u16, b: i16 };

pub fn packedUnion(x: u16) i16 {
    const u: PU = .{ .a = x };
    return u.b;
}

pub fn f80Add(a: f80, b: f80) f80 {
    return a + b;
}

pub fn boolLanes(a: bool, b: bool) bool {
    var v: @Vector(2, bool) = .{ a, b };
    const p: *@Vector(2, bool) = &v;
    return p.*[0];
}

pub fn nibbleLanes(a: u4, b: u4) u4 {
    var v: @Vector(2, u4) = .{ a, b };
    const p: *@Vector(2, u4) = &v;
    return p.*[1];
}

pub const E = enum { one, two };

pub fn tagName(e: E) []const u8 {
    return @tagName(e);
}

pub fn create(a: std.mem.Allocator) !*u32 {
    return a.create(u32);
}

/// `u128` is 8-byte aligned on s390x, 16 in the model: a layout mismatch.
pub fn u128Bytes(x: u128) [16]u8 {
    return @bitCast(x);
}

comptime {
    _ = &atomicRead;
    _ = &packedUnion;
    _ = &f80Add;
    _ = &boolLanes;
    _ = &nibbleLanes;
    _ = &tagName;
    _ = &create;
    _ = &u128Bytes;
}
