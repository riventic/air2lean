//! Runtime operands force AIR permutations; zero-width cases are compiler folded.
pub export fn reverse8(x: u8) u8 { return @bitReverse(x); }
pub export fn reverseSigned8(x: i8) u8 { return @bitCast(@bitReverse(x)); }
pub export fn reverse1(x: u8) u8 { return @bitReverse(@as(u1, @truncate(x))); }
pub export fn reverse3(x: u8) u8 { return @bitReverse(@as(u3, @truncate(x))); }
pub export fn reverseSigned3(x: i8) u8 { return @as(u3, @bitCast(@bitReverse(@as(i3, @truncate(x))))); }
pub export fn reverse9(x: u16) u16 { return @bitReverse(@as(u9, @truncate(x))); }
pub export fn reverseSigned9(x: i16) u16 { return @as(u9, @bitCast(@bitReverse(@as(i9, @truncate(x))))); }
pub export fn swap8(x: u8) u8 { return @byteSwap(x); }
pub export fn swapSigned8(x: i8) u8 { return @bitCast(@byteSwap(x)); }
pub export fn swap16(x: u16) u16 { return @byteSwap(x); }
pub export fn swapSigned16(x: i16) u16 { return @bitCast(@byteSwap(x)); }
pub export fn swap24(x: u32) u32 { return @byteSwap(@as(u24, @truncate(x))); }
pub export fn swapSigned24(x: i32) u32 { return @as(u24, @bitCast(@byteSwap(@as(i24, @truncate(x))))); }
pub export fn reverse64(x: u64) u64 { return @bitReverse(x); }
pub export fn reverseSigned64(x: i64) u64 { return @bitCast(@bitReverse(x)); }
pub export fn swap64(x: u64) u64 { return @byteSwap(x); }
pub export fn swapSigned64(x: i64) u64 { return @bitCast(@byteSwap(x)); }
pub export fn reverse128(x: u128) u128 { return @bitReverse(x); }
pub export fn reverseSigned128(x: i128) u128 { return @bitCast(@bitReverse(x)); }
pub export fn swap128(x: u128) u128 { return @byteSwap(x); }
pub export fn swapSigned128(x: i128) u128 { return @bitCast(@byteSwap(x)); }
pub export fn reverseLanes(x: @Vector(3, u16)) @Vector(3, u16) { return @bitReverse(x); }
pub export fn reverseSignedLanes(x: @Vector(3, i16)) @Vector(3, i16) { return @bitReverse(x); }
pub export fn swapLanes(x: @Vector(3, u16)) @Vector(3, u16) { return @byteSwap(x); }
pub export fn swapSignedLanes(x: @Vector(3, i16)) @Vector(3, i16) { return @byteSwap(x); }
pub export fn reverseNarrowLanes(x: @Vector(3, u8)) @Vector(3, u8) {
    return @bitReverse(@as(@Vector(3, u3), @truncate(x)));
}
pub export fn reverseZero() u0 { return @bitReverse(@as(u0, 0)); }
pub export fn reverseSignedZero() i0 { return @bitReverse(@as(i0, 0)); }
pub export fn swapZero() u0 { return @byteSwap(@as(u0, 0)); }
pub export fn swapSignedZero() i0 { return @byteSwap(@as(i0, 0)); }
