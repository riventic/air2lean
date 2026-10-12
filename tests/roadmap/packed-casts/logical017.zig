//! L07: Zig 0.17.0 `@bitCast` in logical bit order of aggregates whose elements are not plain
//! integers or `bool`s: nested arrays, arrays and vectors of floats, enums, packed structs and
//! packed unions, and packed unions to and from arrays of narrower items. Each cast is a compile
//! error (bit-size mismatch) or a different memory reinterpretation on Zig 0.16.0 and older.
pub const Mode = enum(u2) { off, low, high };
pub const Half = packed struct(u16) { lo: u8, hi: u8 };
pub const U = packed union { i: u16, h: f16, p: Half };
pub const Nib = packed struct(u6) { a: u2, m: Mode, b: u2 };
pub const FH = packed struct(u32) { lo: f16, hi: u16 };

pub fn nestedToInt(a: [2][3]u4) u24 {
    return @bitCast(a);
}

pub fn intToNested(x: u24) [2][3]u4 {
    return @bitCast(x);
}

pub fn modesToInt(a: [4]Mode) u8 {
    return @bitCast(a);
}

pub fn intToModes(x: u8) [4]Mode {
    return @bitCast(x);
}

pub fn nibsToInt(a: [3]Nib) u18 {
    return @bitCast(a);
}

pub fn intToNibs(x: u18) [3]Nib {
    return @bitCast(x);
}

pub fn unionsToInt(a: [2]U) u32 {
    return @bitCast(a);
}

pub fn uToNibbles(u: U) [4]u4 {
    return @bitCast(u);
}

pub fn nibblesToU(a: [4]u4) U {
    return @bitCast(a);
}

pub fn halvesToVec(a: [2]f16) @Vector(4, u8) {
    return @bitCast(a);
}

pub fn vecToHalves(v: @Vector(2, f16)) [2]Half {
    return @bitCast(v);
}

pub fn floatsToNested(a: [2]f16) [2][2]u8 {
    return @bitCast(a);
}

/// A packed struct with a float field to bytes: a NaN field's bits are `.unspecified`.
pub fn fhToBytes(x: FH) [4]u8 {
    return @bitCast(x);
}

comptime {
    _ = &fhToBytes;
    _ = &nestedToInt;
    _ = &intToNested;
    _ = &modesToInt;
    _ = &intToModes;
    _ = &nibsToInt;
    _ = &intToNibs;
    _ = &unionsToInt;
    _ = &uToNibbles;
    _ = &nibblesToU;
    _ = &halvesToVec;
    _ = &vecToHalves;
    _ = &floatsToNested;
}
