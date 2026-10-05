//! Integer bit counts, signed shift overflow, narrow widths, and production-style bitsets.
pub export fn counts8(x: u8) u32 {
    return @as(u32, @clz(x)) | (@as(u32, @ctz(x)) << 8) | (@as(u32, @popCount(x)) << 16);
}
pub export fn countsSigned8(x: i8) u32 {
    return @as(u32, @clz(x)) | (@as(u32, @ctz(x)) << 8) | (@as(u32, @popCount(x)) << 16);
}
pub export fn countsNarrow(x: u8) u32 {
    const a: u3 = @truncate(x);
    return @as(u32, @clz(a)) | (@as(u32, @ctz(a)) << 8) | (@as(u32, @popCount(a)) << 16);
}
pub export fn countsOne(x: u8) u32 {
    const a: u1 = @truncate(x);
    return @as(u32, @clz(a)) | (@as(u32, @ctz(a)) << 8) | (@as(u32, @popCount(a)) << 16);
}
pub export fn shiftUnsigned8(x: u8, amount: u8) u16 {
    const r = @shlWithOverflow(x, @as(u3, @truncate(amount)));
    return @as(u16, r[0]) | (@as(u16, r[1]) << 8);
}
pub export fn shiftSigned8(x: i8, amount: u8) u16 {
    const r = @shlWithOverflow(x, @as(u3, @truncate(amount)));
    return @as(u16, @as(u8, @bitCast(r[0]))) | (@as(u16, r[1]) << 8);
}
pub export fn shiftNarrow(x: u8, amount: u8) u8 {
    const r = @shlWithOverflow(@as(u3, @truncate(x)), @as(u2, @truncate(amount)));
    return @as(u8, r[0]) | (@as(u8, r[1]) << 3);
}
pub export fn shiftSignedNarrow(x: i8, amount: u8) u8 {
    const r = @shlWithOverflow(@as(i3, @truncate(x)), @as(u2, @truncate(amount)));
    return @as(u8, @as(u3, @bitCast(r[0]))) | (@as(u8, r[1]) << 3);
}
pub export fn leadingLanes(x: @Vector(4, u8)) @Vector(4, u8) {
    return @intCast(@clz(x));
}
pub export fn trailingLanes(x: @Vector(4, i8)) @Vector(4, u8) {
    return @intCast(@ctz(x));
}
pub export fn populationLanes(x: @Vector(4, u8)) @Vector(4, u8) {
    return @intCast(@popCount(x));
}
pub export fn shiftLanes(x: @Vector(4, u8), amount: @Vector(4, u8)) @Vector(4, u16) {
    const r = @shlWithOverflow(x, @as(@Vector(4, u3), @truncate(amount)));
    return @as(@Vector(4, u16), @intCast(r[0])) |
        (@as(@Vector(4, u16), @intCast(r[1])) << @as(@Vector(4, u4), @splat(8)));
}
pub export fn shiftSignedLanes(x: @Vector(4, i8), amount: @Vector(4, u8)) @Vector(4, i16) {
    const r = @shlWithOverflow(x, @as(@Vector(4, u3), @truncate(amount)));
    const bits = @as(@Vector(4, i16), @intCast(r[0])) & @as(@Vector(4, i16), @splat(255));
    return bits | (@as(@Vector(4, i16), @intCast(r[1])) << @as(@Vector(4, u4), @splat(8)));
}
/// The empty bitset has no first index; 64 is its sentinel.
pub export fn firstSet(x: u64) u32 {
    if (x == 0) return 64;
    return @ctz(x);
}
pub export fn clearLowest(x: u64) u64 {
    return x & (x -% 1);
}
pub export fn cardinality(x: u64) u32 {
    return @popCount(x);
}
