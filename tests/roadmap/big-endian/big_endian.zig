//! T03: one source, exported for s390x-linux (big endian) and x86_64-linux (little endian).
//! Every function observes byte order: a byte view of an integer, a float, a packed struct, a
//! vector or an `extern` aggregate, or a bit-pointer store into a packed struct's memory.
const std = @import("std");

pub const P = packed struct(u32) { a: u4, b: u12, c: u16 };
pub const Q = packed struct(u16) { lo: u12, hi: u4 };
pub const S = extern struct { a: u16, b: u16, c: u32 };
pub const U = extern union { w: u32, h: [2]u16, b: [4]u8 };

pub fn u32ToBytes(x: u32) [4]u8 {
    return @bitCast(x);
}

pub fn bytesToU32(b: [4]u8) u32 {
    return @bitCast(b);
}

pub fn i16ToBytes(x: i16) [2]u8 {
    return @bitCast(x);
}

pub fn u64ToHalves(x: u64) [2]u32 {
    return @bitCast(x);
}

pub fn f32ToBytes(x: f32) [4]u8 {
    return @bitCast(x);
}

pub fn bytesToF64Bits(b: [8]u8) u64 {
    const f: f64 = @bitCast(b);
    return @bitCast(f);
}

pub fn f16ToBytes(x: f16) [2]u8 {
    return @bitCast(x);
}

pub fn packedToBytes(x: u32) [4]u8 {
    const p: P = @bitCast(x);
    return @bitCast(p);
}

pub fn packed16ToBytes(lo: u12, hi: u4) [2]u8 {
    const q: Q = .{ .lo = lo, .hi = hi };
    return @bitCast(q);
}

/// A bit-pointer store into a packed struct in memory, then the struct's memory bytes.
pub fn setFieldBytes(x: u32, v: u12) [4]u8 {
    var p: P = @bitCast(x);
    const f: *align(4:4:4) u12 = &p.b;
    f.* = v;
    const bytes: *const [4]u8 = @ptrCast(&p);
    return bytes.*;
}

/// A bit-pointer load after the bytes of the packed struct were written one by one.
pub fn fieldFromBytes(b0: u8, b1: u8, b2: u8, b3: u8) u12 {
    var p: P = @bitCast(@as(u32, 0));
    const bytes: *[4]u8 = @ptrCast(&p);
    bytes[0] = b0;
    bytes[1] = b1;
    bytes[2] = b2;
    bytes[3] = b3;
    const f: *align(4:4:4) const u12 = &p.b;
    return f.*;
}

/// Byte `i` of a `u32` in memory.
pub fn byteOfU32(x: u32, i: usize) u8 {
    var v = x;
    const bytes: *const [4]u8 = @ptrCast(&v);
    return bytes[i];
}

/// A `u16` assembled from two stored bytes.
pub fn u16FromStoredBytes(b0: u8, b1: u8) u16 {
    var v: [2]u8 align(2) = .{ b0, b1 };
    const w: *const u16 = @ptrCast(&v);
    return w.*;
}

/// Byte `i` of an `f64` in memory.
pub fn byteOfF64(x: f64, i: usize) u8 {
    var v = x;
    const bytes: *const [8]u8 = @ptrCast(&v);
    return bytes[i];
}

pub fn vecToBytes(a: u16, b: u16) [4]u8 {
    const v: @Vector(2, u16) = .{ a, b };
    return @bitCast(v);
}

pub fn bytesToVecLane0(b: [8]u8) u32 {
    const v: @Vector(2, u32) = @bitCast(b);
    return v[0];
}

pub fn externToBytes(a: u16, b: u16, c: u32) [8]u8 {
    const s: S = .{ .a = a, .b = b, .c = c };
    return @bitCast(s);
}

/// The first `u16` of an `extern union` written as a `u32`.
pub fn unionHalf(x: u32) u16 {
    const u: U = .{ .w = x };
    return u.h[0];
}

pub fn unionByte(x: u32, i: usize) u8 {
    const u: U = .{ .w = x };
    return u.b[i];
}

comptime {
    _ = &u32ToBytes;
    _ = &bytesToU32;
    _ = &i16ToBytes;
    _ = &u64ToHalves;
    _ = &f32ToBytes;
    _ = &bytesToF64Bits;
    _ = &f16ToBytes;
    _ = &packedToBytes;
    _ = &packed16ToBytes;
    _ = &setFieldBytes;
    _ = &fieldFromBytes;
    _ = &byteOfU32;
    _ = &u16FromStoredBytes;
    _ = &byteOfF64;
    _ = &vecToBytes;
    _ = &bytesToVecLane0;
    _ = &externToBytes;
    _ = &unionHalf;
    _ = &unionByte;
}
