//! Encode/decode exactness (docs/architecture-audit/enc-exactness.md): integers with padding bits
//! read from bytes that a store of that type did not write, and written then read as bytes. Zig
//! 0.17.0 stores such an integer zero- or sign-extended to its ABI size and loads it with
//! `trunc nuw`/`trunc nsw` (poison unless the padding is that extension); up to 0.16.0 a store
//! leaves the padding unspecified and a load ignores it. `native.zig` prints each case.
const std = @import("std");

var w16: u16 = 0;
var w32: u32 = 0;

const E24 = enum(u24) { a = 5, b = 0x80_0000, _ };

/// The bytes of the `u16` `x` read as an `i10`: 0x0200 has the sign bit set and zero padding.
pub fn i10ZeroPad(x: u16) i16 {
    w16 = x;
    return @as(*const i10, @ptrCast(&w16)).*;
}

/// The bytes of the `u32` `x` read as a `u24`: 0x01000005 has a padding bit set.
pub fn u24SetPad(x: u32) u32 {
    w32 = x;
    return @as(*const u24, @ptrCast(&w32)).*;
}

/// The bytes of the `u32` `x` read as an `i24`: 0x00800000 has the sign bit set and zero padding.
pub fn i24ZeroPad(x: u32) i32 {
    w32 = x;
    return @as(*const i24, @ptrCast(&w32)).*;
}

/// The bytes of the `u32` `x` read as an `enum(u24)`.
pub fn e24SetPad(x: u32) u32 {
    w32 = x;
    return @intFromEnum(@as(*const E24, @ptrCast(&w32)).*);
}

/// An `i10` stored over 0xffff and read back as the `u16` of its bytes.
pub fn i10StoreBytes(v: i10) u16 {
    w16 = 0xffff;
    @as(*i10, @ptrCast(&w16)).* = v;
    return w16;
}

/// A `u24` stored over 0xffffffff and read back as the `u32` of its bytes.
pub fn u24StoreBytes(v: u24) u32 {
    w32 = 0xffff_ffff;
    @as(*u24, @ptrCast(&w32)).* = v;
    return w32;
}

/// An `i24` stored and read back as an `i24`: exact at every version.
pub fn i24RoundTrip(v: i24) i32 {
    @as(*i24, @ptrCast(&w32)).* = v;
    return @as(*const i24, @ptrCast(&w32)).*;
}

/// The bytes of a `bool` read as a `u8`.
pub fn boolByte(b: bool) u8 {
    w16 = 0xffff;
    @as(*bool, @ptrCast(&w16)).* = b;
    return @truncate(w16);
}

comptime {
    _ = &i10ZeroPad;
    _ = &u24SetPad;
    _ = &i24ZeroPad;
    _ = &e24SetPad;
    _ = &i10StoreBytes;
    _ = &u24StoreBytes;
    _ = &i24RoundTrip;
    _ = &boolByte;
}
