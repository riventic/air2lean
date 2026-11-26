//! L09 probe of the element-stride vector layout (the self-hosted x86_64 backend,
//! `-fno-llvm -target x86_64-linux -mcpu=baseline`): an integer or float lane sits at its ABI
//! stride, as in `[n]T`, and the vector is padded to its alignment; a `bool` vector is bit-packed.
//! `ModelStrided.lean` prints the same lines from `ZigLean/VecStride.lean`.
//!
//! * `layout T n size align`: `@sizeOf`/`@alignOf` of `@Vector(n, T)`.
//! * `vector NAME size align BYTES`: the image after a store of every lane through `v[i] = x`.
//! * `whole NAME BYTES`: the image after a load and a store of that whole vector.
//! * `lane NAME i BYTES`: the image after a store through `&v[i]`.
//! * `load NAME j X`: a load through `&v[j]`, `j` the lane after `i`.
//! * `cell NAME i BYTES` (integer and float lanes): every byte set to a5, then a store through
//!   `&v[i]`: it writes the bytes of lane `i` only.
//!
//! A byte the model leaves undefined prints as `--`: a byte after the lanes, a byte after a float
//! lane's bits (`f80`: 10 of 16 bytes), and the bytes after a `bool` vector's bits, whose last
//! byte prints without its unused high bits. An integer lane's padding bits print as stored (the
//! backend stores the extension of the value, `Zig.intEncExt`).
const std = @import("std");

fn rt(comptime T: type, value: T) T {
    var storage = value;
    const pointer: *volatile T = &storage;
    return pointer.*;
}

fn print(comptime fmt: []const u8, args: anytype) void {
    std.debug.print(fmt, args);
}

fn image(comptime N: comptime_int, comptime T: type, value: *const @Vector(N, T)) void {
    const V = @Vector(N, T);
    const bytes: *const volatile [@sizeOf(V)]u8 = @ptrCast(value);
    for (0..@sizeOf(V)) |k| {
        if (T == bool) {
            if (8 * k >= N) {
                print(" --", .{});
            } else {
                const used = @min(8, N - 8 * k);
                const mask: u8 = @truncate((@as(u16, 1) << @intCast(used)) - 1);
                print(" {x:0>2}", .{bytes[k] & mask});
            }
        } else if (k >= N * @sizeOf(T) or
            (@typeInfo(T) == .float and k % @sizeOf(T) >= (@bitSizeOf(T) + 7) / 8))
        {
            print(" --", .{});
        } else {
            print(" {x:0>2}", .{bytes[k]});
        }
    }
    print("\n", .{});
}

fn laneBits(comptime T: type, x: T) u128 {
    return if (T == bool) @intFromBool(x) else @as(std.math.IntFittingRange(0, (1 << @bitSizeOf(T)) - 1), @bitCast(x));
}

fn probe(comptime name: []const u8, comptime N: comptime_int, comptime T: type, lanes: [N]T,
    comptime lane: usize, new: T) void {
    const V = @Vector(N, T);
    var v: V = undefined;
    inline for (0..N) |i| v[i] = rt(T, lanes[i]);
    print("vector {s} {d} {d}", .{ name, @sizeOf(V), @alignOf(V) });
    image(N, T, &v);
    var w: V = undefined;
    w = rt(V, v);
    print("whole {s}", .{name});
    image(N, T, &w);
    const pointer = &v[lane];
    pointer.* = rt(T, new);
    print("lane {s} {d}", .{ name, lane });
    image(N, T, &v);
    const j = (lane + 1) % N;
    const q = &w[j];
    print("load {s} {d} {x}\n", .{ name, j, laneBits(T, rt(T, q.*)) });
    if (T == bool) return;
    const bytes: *volatile [@sizeOf(V)]u8 = @ptrCast(&w);
    for (0..@sizeOf(V)) |k| bytes[k] = 0xa5;
    const cell = &w[lane];
    cell.* = rt(T, new);
    print("cell {s} {d}", .{ name, lane });
    for (0..@sizeOf(V)) |k| {
        const c = k % @sizeOf(T);
        if (k / @sizeOf(T) == lane and @typeInfo(T) == .float and c >= (@bitSizeOf(T) + 7) / 8) {
            print(" --", .{});
        } else {
            print(" {x:0>2}", .{bytes[k]});
        }
    }
    print("\n", .{});
}

fn layouts(comptime name: []const u8, comptime T: type, comptime counts: []const comptime_int) void {
    inline for (counts) |n| {
        const V = @Vector(n, T);
        print("layout {s} {d} {d} {d}\n", .{ name, n, @sizeOf(V), @alignOf(V) });
    }
}

const small = blk: {
    var counts: [41]comptime_int = undefined;
    for (0..41) |i| counts[i] = i;
    break :blk counts;
};

pub fn main() void {
    inline for (.{ u1, u4, u7, u8, u9, i9, u12, u16, u24, u32, u40, u64, u65, u128, f16, f32, f64, f80, f128 }) |T|
        layouts(@typeName(T), T, &small);
    layouts("bool", bool, &small);
    layouts("bool", bool, &.{ 63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512, 513 });
    probe("u9x4", 4, u9, .{ 0x1ff, 0, 0x1ff, 1 }, 2, 0x0aa);
    probe("i9x2", 2, i9, .{ -1, 1 }, 1, -2);
    probe("u12x3", 3, u12, .{ 0xabc, 0x123, 0xfff }, 0, 0x555);
    probe("u4x4", 4, u4, .{ 1, 2, 3, 4 }, 3, 0xf);
    probe("u1x8", 8, u1, .{ 1, 0, 1, 0, 0, 0, 0, 1 }, 6, 1);
    probe("u24x2", 2, u24, .{ 0xabcdef, 0x123456 }, 0, 0x000001);
    probe("i24x3", 3, i24, .{ -2, 0x123456, -0x800000 }, 1, -0x012346);
    probe("u40x2", 2, u40, .{ 0xaabbccddee, 0x1122334455 }, 1, 0x0102030405);
    probe("u8x3", 3, u8, .{ 1, 2, 3 }, 2, 0xff);
    probe("u16x3", 3, u16, .{ 1, 0x8000, 3 }, 0, 0xbeef);
    probe("u32x3", 3, u32, .{ 1, 2, 3 }, 1, 0xdeadbeef);
    probe("u64x3", 3, u64, .{ 1, 0x8000000000000000, 3 }, 2, 0x0123456789abcdef);
    probe("f32x3", 3, f32, .{ 1.0, -2.0, 0.5 }, 1, 3.0);
    probe("f80x2", 2, f80, .{ 1.0, -2.0 }, 0, 0.5);
    probe("bool5", 5, bool, .{ true, false, true, true, false }, 1, true);
    probe("bool16", 16, bool, .{ true, false, true, true, false, true, false, false, false, false, false, false, false, false, false, true }, 15, false);
}
