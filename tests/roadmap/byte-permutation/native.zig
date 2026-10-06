const std = @import("std");
const permutations = @import("permutations");
pub fn main() void {
    for (0..256) |i| {
        const x: u8 = @intCast(i);
        const sx: i8 = @bitCast(x);
        std.debug.print("small {d} {d} {d} {d} {d} {d} {d} {d}\n", .{ i,
            permutations.reverse8(x), permutations.reverseSigned8(sx), permutations.reverse1(x),
            permutations.reverse3(x), permutations.reverseSigned3(sx), permutations.swap8(x), permutations.swapSigned8(sx) });
    }
    for (0..512) |i| {
        const x: u16 = @intCast(i);
        const sx: i16 = @bitCast(x);
        std.debug.print("nine {d} {d} {d}\n", .{ i, permutations.reverse9(x), permutations.reverseSigned9(sx) });
    }
    const words = [_]u32{ 0, 1, 0x1234, 0x8001, 0xffff, 0x123456, 0x800001, 0xffffff, 0xffffffff };
    for (words) |x| {
        const y: u16 = @truncate(x);
        std.debug.print("word {d} {d} {d} {d} {d}\n", .{ x, permutations.swap16(y),
            permutations.swapSigned16(@bitCast(y)), permutations.swap24(x), permutations.swapSigned24(@bitCast(x)) });
    }
    const wide = [_]u128{ 0, 1, 0x0123456789abcdef, 0x8000000000000001,
        0xffffffffffffffff, 0x0123456789abcdeffedcba9876543210,
        0x80000000000000000000000000000001, 0xffffffffffffffffffffffffffffffff };
    for (wide) |x| {
        const y: u64 = @truncate(x);
        std.debug.print("wide {d} {d} {d} {d} {d} {d} {d} {d} {d}\n", .{ x,
            permutations.reverse64(y), permutations.reverseSigned64(@bitCast(y)),
            permutations.swap64(y), permutations.swapSigned64(@bitCast(y)),
            permutations.reverse128(x), permutations.reverseSigned128(@bitCast(x)),
            permutations.swap128(x), permutations.swapSigned128(@bitCast(x)) });
    }
    const vectors = [_]@Vector(3, u16){ .{ 0x1234, 0x8001, 0x00ff }, .{ 1, 2, 3 }, .{ 0, 65535, 256 } };
    for (vectors, 0..) |x, i| {
        const a = permutations.reverseLanes(x);
        const b = permutations.reverseSignedLanes(@bitCast(x));
        const c = permutations.swapLanes(x);
        const d = permutations.swapSignedLanes(@bitCast(x));
        const e = permutations.reverseNarrowLanes(@truncate(x));
        inline for (0..3) |lane| {
            const ub: u16 = @bitCast(b[lane]);
            const ud: u16 = @bitCast(d[lane]);
            std.debug.print("lane {d} {d} {d} {d} {d} {d} {d}\n", .{ i, lane, a[lane], ub, c[lane], ud, e[lane] });
        }
    }
    std.debug.print("zero {d} {d} {d} {d}\n", .{ permutations.reverseZero(),
        permutations.reverseSignedZero(), permutations.swapZero(), permutations.swapSignedZero() });
}
