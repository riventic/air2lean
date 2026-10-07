//! L09 vector memory-layout probe: the size, alignment and in-memory bytes of vectors whose
//! lanes are not byte-strided (u9, u12, u24, u40, i9, f80, bool) and of byte-lane controls,
//! before and after a store through a lane pointer. A byte past the lanes' bits prints as `--`
//! and the unused high bits of the last value byte are cleared: both are padding, which the
//! model leaves undefined. `Model.lean` prints the same lines from the Lean encoding.
const std = @import("std");

fn rt(comptime T: type, value: T) T {
    var storage = value;
    const pointer: *volatile T = &storage;
    return pointer.*;
}

fn image(comptime T: type, value: *const T, out: anytype) void {
    const bits = @bitSizeOf(T);
    const bytes: *const [@sizeOf(T)]u8 = @ptrCast(value);
    const volatile_bytes: *const volatile [@sizeOf(T)]u8 = bytes;
    for (0..@sizeOf(T)) |i| {
        if (8 * i >= bits) {
            out.print(" --", .{});
        } else {
            const used = @min(8, bits - 8 * i);
            const mask: u8 = @truncate((@as(u16, 1) << @intCast(used)) - 1);
            out.print(" {x:0>2}", .{volatile_bytes[i] & mask});
        }
    }
    out.print("\n", .{});
}

const Out = struct {
    fn print(_: Out, comptime fmt: []const u8, args: anytype) void {
        std.debug.print(fmt, args);
    }
};

fn probe(comptime name: []const u8, comptime N: comptime_int, comptime T: type, lanes: [N]T,
    comptime lane: usize, new: T) void {
    const V = @Vector(N, T);
    const out = Out{};
    var v: V = undefined;
    inline for (0..N) |i| v[i] = rt(T, lanes[i]);
    out.print("vector {s} {d} {d}", .{ name, @sizeOf(V), @alignOf(V) });
    image(V, &v, out);
    const pointer = &v[lane];
    pointer.* = rt(T, new);
    out.print("lane {s} {d}", .{ name, lane });
    image(V, &v, out);
}

pub fn main() void {
    probe("u9x4", 4, u9, .{ 0x1ff, 0, 0x1ff, 1 }, 2, 0x0aa);
    probe("i9x2", 2, i9, .{ -1, 1 }, 1, -2);
    probe("u12x3", 3, u12, .{ 0xabc, 0x123, 0xfff }, 0, 0x555);
    probe("u4x4", 4, u4, .{ 1, 2, 3, 4 }, 3, 0xf);
    probe("u1x8", 8, u1, .{ 1, 0, 1, 0, 0, 0, 0, 1 }, 6, 1);
    probe("u24x2", 2, u24, .{ 0xabcdef, 0x123456 }, 0, 0x000001);
    probe("u24x3", 3, u24, .{ 0xabcdef, 0x123456, 0x777777 }, 1, 0xfedcba);
    probe("u40x2", 2, u40, .{ 0xaabbccddee, 0x1122334455 }, 1, 0x0102030405);
    probe("f80x2", 2, f80, .{ 1.0, -2.0 }, 0, 0.5);
    probe("bool5", 5, bool, .{ true, false, true, true, false }, 1, true);
    probe("bool16", 16, bool, .{ true, false, true, true, false, true, false, false, false, false, false, false, false, false, false, true }, 15, false);
    probe("u8x3", 3, u8, .{ 1, 2, 3 }, 2, 0xff);
    probe("u16x3", 3, u16, .{ 1, 0x8000, 3 }, 0, 0xbeef);
    probe("u32x3", 3, u32, .{ 1, 2, 3 }, 1, 0xdeadbeef);
}
