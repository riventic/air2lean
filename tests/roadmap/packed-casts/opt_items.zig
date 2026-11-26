//! L07: Zig 0.14.1 and 0.15.2 check only the outer types of a `@bitCast`, so an array of
//! non-pointer optionals is a memory reinterpretation: each item is its payload at offset 0, a
//! flag byte (1: a value, 0: null) at the payload's size, then padding to the payload's
//! alignment (`Enc (Option α)`). The payload is any type the model has in memory: integers of
//! several widths (`u0`, a padded `u12` and `u24`, signed), `bool`, floats, an enum, arrays,
//! optionals, `extern`, packed and `auto` structs, vectors. A null item's payload bytes and the
//! padding are undefined. Zig 0.16.0 and 0.17.1 reject these casts (`compile-errors/`).
pub const E = enum(u8) { a, b, c };
pub const ES = extern struct { a: u8, b: u8 };
pub const PS = packed struct(u16) { lo: u4, hi: u12 };
pub const S = struct { a: u16, b: u8 };

/// Two items without padding: every byte is defined unless an item is null.
pub fn u8sToInt(a: [2]?u8) u32 {
    return @bitCast(a);
}
/// Item 1 of `x` (0x100: null).
pub fn intToU8s(x: u32) u16 {
    const a: [2]?u8 = @bitCast(x);
    return if (a[1]) |v| v else 0x100;
}
/// `?u16` has a padding byte after its flag: the integer is `.unspecified`.
pub fn u16sToInt(a: [2]?u16) u64 {
    return @bitCast(a);
}
/// Item 1's payload (0x10000: null); the padding bytes of `x` are ignored.
pub fn intToU16s(x: u64) u32 {
    const a: [2]?u16 = @bitCast(x);
    return if (a[1]) |v| v else 0x10000;
}
/// `?u0` is its flag byte.
pub fn zerosToInt(a: [4]?u0) u32 {
    return @bitCast(a);
}
/// The non-null items of `x`.
pub fn intToZeros(x: u32) u8 {
    const a: [4]?u0 = @bitCast(x);
    var n: u8 = 0;
    for (a) |o| {
        if (o != null) n += 1;
    }
    return n;
}
/// `?u12`: two payload bytes (four bits unused), the flag byte, a padding byte.
pub fn intToU12s(x: u64) u16 {
    const a: [2]?u12 = @bitCast(x);
    return if (a[0]) |v| v else 0x1000;
}
/// `?u24`: four payload bytes (one padding), the flag at offset 4.
pub fn intToU24s(x: u128) u32 {
    const a: [2]?u24 = @bitCast(x);
    return if (a[1]) |v| v else 0x1000000;
}
/// `?i8`: item 1 sign-extended (0x100: null).
pub fn intToI8s(x: u32) i16 {
    const a: [2]?i8 = @bitCast(x);
    return if (a[1]) |v| v else 0x100;
}
/// `?u64`: the flag at offset 8 of 16 bytes.
pub fn intToU64(x: u128) u64 {
    const a: [1]?u64 = @bitCast(x);
    return a[0] orelse 0;
}
/// `?u128`: the flag at offset 16 of 32 bytes.
pub fn intToU128(x: u256) u128 {
    const a: [1]?u128 = @bitCast(x);
    return a[0] orelse 0;
}
pub fn boolsToInt(a: [2]?bool) u32 {
    return @bitCast(a);
}
/// Item 0 and 1 as 0 (null), 1 (false) or 2 (true): `3·a[0] + a[1]`.
pub fn intToBools(x: u32) u8 {
    const a: [2]?bool = @bitCast(x);
    var n: u8 = 0;
    for (a) |o| n = 3 * n + if (o) |b| @as(u8, if (b) 2 else 1) else 0;
    return n;
}
/// Floats: the payload's bits (0: null).
pub fn intToF16(x: u32) u16 {
    const a: [1]?f16 = @bitCast(x);
    return if (a[0]) |v| @bitCast(v) else 0;
}
pub fn intToF32(x: u64) u32 {
    const a: [1]?f32 = @bitCast(x);
    return if (a[0]) |v| @bitCast(v) else 0;
}
pub fn intToF64(x: u128) u64 {
    const a: [1]?f64 = @bitCast(x);
    return if (a[0]) |v| @bitCast(v) else 0;
}
pub fn intToF80(x: u256) u80 {
    const a: [1]?f80 = @bitCast(x);
    return if (a[0]) |v| @bitCast(v) else 0;
}
pub fn intToF128(x: u256) u128 {
    const a: [1]?f128 = @bitCast(x);
    return if (a[0]) |v| @bitCast(v) else 0;
}
pub fn enumsToInt(a: [2]?E) u32 {
    return @bitCast(a);
}
/// Item 1's tag (0xff: null).
pub fn intToEnums(x: u32) u8 {
    const a: [2]?E = @bitCast(x);
    return if (a[1]) |v| @intFromEnum(v) else 0xff;
}
/// Arrays as payloads: `?[3]u8` is four bytes.
pub fn arraysToInt(a: [2]?[3]u8) u64 {
    return @bitCast(a);
}
pub fn intToArrays(x: u64) u32 {
    const a: [2]?[3]u8 = @bitCast(x);
    return if (a[1]) |v| @as(u24, @bitCast(v)) else 0x1000000;
}
/// Optionals as array items in a nested array.
pub fn gridToInt(a: [2][2]?u8) u64 {
    return @bitCast(a);
}
pub fn intToGrid(x: u64) u16 {
    const a: [2][2]?u8 = @bitCast(x);
    return if (a[1][0]) |v| v else 0x100;
}
/// `??u8`: the inner optional's two bytes, the outer flag.
pub fn nestedToInt(a: [2]??u8) u48 {
    return @bitCast(a);
}
/// Item 1: 0x200 null, 0x100 a null `?u8`, else the byte.
pub fn intToNested(x: u48) u16 {
    const a: [2]??u8 = @bitCast(x);
    const o = a[1] orelse return 0x200;
    return o orelse 0x100;
}
/// `extern`, packed and `auto` structs and a vector as payloads.
pub fn intToExtern(x: u48) u16 {
    const a: [2]?ES = @bitCast(x);
    return if (a[1]) |v| @as(u16, v.a) << 8 | v.b else 0xffff;
}
pub fn intToPacked(x: u64) u16 {
    const a: [2]?PS = @bitCast(x);
    return if (a[1]) |v| v.hi else 0xffff;
}
pub fn intToAuto(x: u96) u16 {
    const a: [2]?S = @bitCast(x);
    return if (a[1]) |v| v.a +% v.b else 0xffff;
}
/// `?@Vector(4, u32)`: 16 payload bytes, the flag at offset 16 (lane 1; 0: null).
pub fn intToVector(x: u256) u32 {
    const a: [1]?@Vector(4, u32) = @bitCast(x);
    return if (a[0]) |v| v[1] else 0;
}
comptime {
    _ = &u8sToInt;
    _ = &intToU8s;
    _ = &u16sToInt;
    _ = &intToU16s;
    _ = &zerosToInt;
    _ = &intToZeros;
    _ = &intToU12s;
    _ = &intToU24s;
    _ = &intToI8s;
    _ = &intToU64;
    _ = &intToU128;
    _ = &boolsToInt;
    _ = &intToBools;
    _ = &intToF16;
    _ = &intToF32;
    _ = &intToF64;
    _ = &intToF80;
    _ = &intToF128;
    _ = &enumsToInt;
    _ = &intToEnums;
    _ = &arraysToInt;
    _ = &intToArrays;
    _ = &gridToInt;
    _ = &intToGrid;
    _ = &nestedToInt;
    _ = &intToNested;
    _ = &intToExtern;
    _ = &intToPacked;
    _ = &intToAuto;
    _ = &intToVector;
}
