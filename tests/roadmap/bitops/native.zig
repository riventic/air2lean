//! Native reference observations. Build this with --dep bitops -Mroot=... -Mbitops=tests/roadmap/bitops/bitops.zig.
const std = @import("std");
const bitops = @import("bitops");
pub fn main() void {
    for (0..256) |i| {
        const x: u8 = @intCast(i);
        const sx: i8 = @bitCast(x);
        std.debug.print("counts {d} {d} {d} {d} {d}\n", .{ i, bitops.counts8(x), bitops.countsSigned8(sx), bitops.countsNarrow(x), bitops.countsOne(x) });
        for (0..8) |k| {
            const amount: u8 = @intCast(k);
            std.debug.print("shift {d} {d} {d} {d}\n", .{ i, k, bitops.shiftUnsigned8(x, amount), bitops.shiftSigned8(sx, amount) });
        }
        // Count 3 is illegal for u3/i3, so native comparison excludes it.
        for (0..3) |k| {
            const amount: u8 = @intCast(k);
            std.debug.print("narrow {d} {d} {d} {d}\n", .{ i, k, bitops.shiftNarrow(x, amount), bitops.shiftSignedNarrow(sx, amount) });
        }
    }
    const vectors = [_]@Vector(4, u8){ .{ 0, 255, 128, 1 }, .{ 2, 64, 127, 129 }, .{ 0, 0, 0, 0 } };
    const shifts: @Vector(4, u8) = .{ 7, 1, 6, 0 };
    for (vectors, 0..) |x, i| {
        const leading = bitops.leadingLanes(x);
        const trailing = bitops.trailingLanes(@bitCast(x));
        const population = bitops.populationLanes(x);
        const shifted = bitops.shiftLanes(x, shifts);
        const signed_shifted = bitops.shiftSignedLanes(@bitCast(x), shifts);
        inline for (0..4) |lane| {
            std.debug.print("vector {d} {d} {d} {d} {d} {d} {d}\n", .{ i, lane, leading[lane], trailing[lane], population[lane], shifted[lane], signed_shifted[lane] });
        }
    }
    const bitsets = [_]u64{ 0, 1, 2, 0xffff, 0xffffffffffffffff, 0x8000000000000000, 0x8000000000000001, 0x5555555555555555 };
    for (bitsets) |x| {
        std.debug.print("bitset {d} {d} {d} {d}\n", .{ x, bitops.firstSet(x), bitops.clearLowest(x), bitops.cardinality(x) });
    }
}
