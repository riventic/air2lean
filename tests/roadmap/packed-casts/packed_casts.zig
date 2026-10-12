//! L07/L08: packed unions and floats as packed-struct fields, and `@bitCast` of packed unions,
//! floats and float arrays/vectors. Every function compiles and gives the same result on Zig
//! 0.14.1, 0.15.2, 0.16.0 and 0.17.0 (`README.md`); `logical017.zig` has the 0.17-only casts.
pub const Mode = enum(u2) { off, low, high };
pub const Half = packed struct(u16) { lo: u8, hi: u8 };
/// Three 16-bit views of one backing integer.
pub const U = packed union { i: u16, h: f16, p: Half };
/// A packed union and a float at bit offsets that are not byte aligned.
pub const R = packed struct(u40) { a: u4, u: U, f: f16, on: bool, mode: Mode, pad: u1 };
/// A 32-bit float at bit 0 of a 64-bit host, then two integer fields.
pub const W = packed struct(u64) { x: f32, y: u3, z: u29 };

var r: R = undefined;
var w: W = undefined;

// Field accesses through bit-pointers (L08).

/// A packed-union field written as a whole, read through its integer view.
pub fn setUnion() u16 {
    r.a = 3;
    r.u = .{ .i = 0x1234 };
    return r.u.i;
}

/// Writing the union field keeps the 4-bit field below it.
pub fn unionKeepsA() u4 {
    r.a = 9;
    r.u = .{ .i = 0xFFFF };
    return r.a;
}

/// A nested packed struct inside the union inside the struct.
pub fn unionHalfHi() u8 {
    r.u = .{ .p = .{ .lo = 0x11, .hi = 0x22 } };
    return r.u.p.hi;
}

/// The float view of the union, read back as integer bits.
pub fn unionFloatView() u16 {
    r.u = .{ .h = 1.0 };
    return r.u.i;
}

/// A float field at bit 20.
pub fn setFloat() u16 {
    r.f = 1.5;
    return @bitCast(r.f);
}

/// Writing the float keeps the `bool` and enum fields above it.
pub fn floatKeepsNeighbours() u8 {
    r.on = true;
    r.mode = .high;
    r.f = -2.0;
    return @as(u8, @intFromBool(r.on)) | (@as(u8, @intFromEnum(r.mode)) << 1);
}

/// A float field written, doubled in place and read.
pub fn floatInPlace(x: f16) f16 {
    r.f = x;
    r.f = r.f * 2;
    return r.f;
}

/// A 32-bit float field between integer stores.
pub fn wideFloat(x: f32) f32 {
    w.y = 5;
    w.x = x;
    w.z = 7;
    return w.x;
}

// Whole-value casts (L07, L08).

pub fn wToInt(x: W) u64 {
    return @bitCast(x);
}

pub fn rToInt(x: R) u40 {
    return @bitCast(x);
}

pub fn intToR(x: u40) R {
    return @bitCast(x);
}

/// A struct literal with a union built from its float view.
pub fn makeR(a: u4, h: f16) u40 {
    const v: R = .{ .a = a, .u = .{ .h = h }, .f = h, .on = false, .mode = .low, .pad = 0 };
    return @bitCast(v);
}

/// A NaN field (`x`) has no determined bits in the model (`.unspecified`); native code gives
/// some NaN's bits.
pub fn floatField(x: f16) u40 {
    const v: R = .{ .a = 1, .u = .{ .i = 2 }, .f = x, .on = false, .mode = .off, .pad = 0 };
    return @bitCast(v);
}

pub fn uToBytes(u: U) [2]u8 {
    return @bitCast(u);
}

pub fn bytesToU(a: [2]u8) U {
    return @bitCast(a);
}

/// Packed union to packed struct.
pub fn uToHalf(u: U) Half {
    return @bitCast(u);
}

/// Packed struct to float.
pub fn halfToF16(h: Half) f16 {
    return @bitCast(h);
}

/// Float to packed union.
pub fn f16ToU(x: f16) U {
    return @bitCast(x);
}

pub fn floatsToInt(a: [2]f32) u64 {
    return @bitCast(a);
}

pub fn intToFloats(x: u64) [2]f32 {
    return @bitCast(x);
}

pub fn vecToInt(v: @Vector(2, f32)) u64 {
    return @bitCast(v);
}

pub fn intToVec(x: u64) @Vector(2, f32) {
    return @bitCast(x);
}

comptime {
    _ = &setUnion;
    _ = &unionKeepsA;
    _ = &unionHalfHi;
    _ = &unionFloatView;
    _ = &setFloat;
    _ = &floatKeepsNeighbours;
    _ = &floatInPlace;
    _ = &wideFloat;
    _ = &wToInt;
    _ = &rToInt;
    _ = &intToR;
    _ = &makeR;
    _ = &floatField;
    _ = &uToBytes;
    _ = &bytesToU;
    _ = &uToHalf;
    _ = &halfToF16;
    _ = &f16ToU;
    _ = &floatsToInt;
    _ = &intToFloats;
    _ = &vecToInt;
    _ = &intToVec;
}
