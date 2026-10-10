//! Source of the compiler exports in `air/<version>` (L07). Each function is one representation
//! `@bitCast` (or optional-pointer conversion) on runtime operands, so the cast is a real AIR
//! instruction and not a comptime fold. Compare with `probe.zig`, the native probe of the same
//! cases. Export with `export.sh`; `air-handwritten/0.16.0` keeps the earlier hand-written AIR.
//! The functions are `pub` and referenced in a `comptime` block: array parameters are not
//! allowed in `export fn`.
pub const Pair = extern struct { a: u32, b: u32 }; // no padding
pub const Padded = extern struct { a: u8, b: u32 }; // bytes 1..3 are padding
pub const Word = extern union { int: u32, bytes: [4]u8 };
pub const Short = extern union { a: u8, b: u32 }; // bytes 1..3 are padding of `a`

pub fn bytesToU32(v: [4]u8) u32 {
    return @bitCast(v);
}
pub fn u32ToBytes(v: u32) [4]u8 {
    return @bitCast(v);
}
pub fn pairToU64(v: Pair) u64 {
    return @bitCast(v);
}
pub fn u64ToPair(v: u64) Pair {
    return @bitCast(v);
}
pub fn bytesToPadded(v: [8]u8) Padded {
    return @bitCast(v);
}
pub fn paddedToBytes(v: Padded) [8]u8 {
    return @bitCast(v);
}
pub fn u24x2ToU56(v: [2]u24) u56 {
    return @bitCast(v);
}
pub fn u56ToU24x2(v: u56) [2]u24 {
    return @bitCast(v);
}
pub fn u32ToWord(v: u32) Word {
    return @bitCast(v);
}
pub fn shortToU32(v: Short) u32 {
    return @bitCast(v);
}

pub fn optAddr(p: ?*u32) usize {
    return @intFromPtr(p);
}
pub fn optFromAddr(a: usize) ?*u32 {
    return @ptrFromInt(a);
}
pub fn optUnwrap(p: ?*u32) *u32 {
    return @ptrCast(p);
}
pub fn ptrWrap(p: *u32) ?*u32 {
    return @ptrCast(p);
}

comptime {
    _ = &bytesToU32; _ = &u32ToBytes; _ = &pairToU64; _ = &u64ToPair; _ = &bytesToPadded;
    _ = &paddedToBytes; _ = &u24x2ToU56; _ = &u56ToU24x2; _ = &u32ToWord; _ = &shortToU32;
    _ = &optAddr; _ = &optFromAddr; _ = &optUnwrap; _ = &ptrWrap;
}
