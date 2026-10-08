//! T04 aarch64 ABI probe: unusual integer widths, f80/f128 layout and results (incl. NaN and
//! subnormal edges), `c_longdouble`, and synchronization boundaries (atomic widths, alignment,
//! results, cache line). One line per observation; `scripts/aarch64-abi.py` compares the output
//! with the versioned expected file of the profile that ran it. Vector layouts are L09's
//! `tests/roadmap/vector-layouts/probe.zig`, run by the same script.
//!
//! An image prints the value's memory bytes, little-endian, `--` for a byte past the value's
//! bits, and the unused high bits of the last value byte cleared (padding: the model leaves it
//! undefined).
const std = @import("std");
const builtin = @import("builtin");
const compat = @import("compat");

/// Hides `x` from LLVM's constant folder, so that each case runs on the target.
fn rt(comptime T: type, x: T) T {
    var v: T = x;
    const p: *volatile T = &v;
    return p.*;
}

fn Bits(comptime T: type) type {
    return std.meta.Int(.unsigned, @bitSizeOf(T));
}

fn hex(out: *std.Io.Writer, comptime T: type, x: T) !void {
    const digits = comptime (@bitSizeOf(T) + 3) / 4;
    try out.print("{x:0>" ++ std.fmt.comptimePrint("{d}", .{digits}) ++ "}", .{@as(Bits(T), @bitCast(x))});
}

fn image(out: *std.Io.Writer, comptime T: type, value: *const T) !void {
    const bits = @bitSizeOf(T);
    const bytes: *const volatile [@sizeOf(T)]u8 = @ptrCast(value);
    for (0..@sizeOf(T)) |i| {
        if (8 * i >= bits) {
            try out.print(" --", .{});
        } else {
            const used = @min(8, bits - 8 * i);
            const mask: u8 = @truncate((@as(u16, 1) << @intCast(used)) - 1);
            try out.print(" {x:0>2}", .{bytes[i] & mask});
        }
    }
    try out.print("\n", .{});
}

/// `int <type> <size> <align> <bits> <image of value>`.
fn int(out: *std.Io.Writer, comptime T: type, value: T) !void {
    var v = rt(T, value);
    try out.print("int {s} {d} {d} {d}", .{ @typeName(T), @sizeOf(T), @alignOf(T), @bitSizeOf(T) });
    try image(out, T, &v);
}

fn intop(out: *std.Io.Writer, comptime T: type, name: []const u8, x: T) !void {
    try out.print("intop {s} {s} ", .{ @typeName(T), name });
    try hex(out, T, x);
    try out.print("\n", .{});
}

/// `float <name> <size> <align> <bits> <image of 1.0>`.
fn float(out: *std.Io.Writer, comptime name: []const u8, comptime T: type) !void {
    var one = rt(T, 1.0);
    try out.print("float {s} {d} {d} {d}", .{ name, @sizeOf(T), @alignOf(T), @bitSizeOf(T) });
    try image(out, T, &one);
}

fn fop(out: *std.Io.Writer, comptime T: type, name: []const u8, x: anytype) !void {
    try out.print("fop {s} {s} ", .{ @typeName(T), name });
    if (@TypeOf(x) == bool) {
        try out.print("{}\n", .{x});
    } else {
        try hex(out, @TypeOf(x), x);
        try out.print("\n", .{});
    }
}

/// Results that Zig leaves to the target, or that a soft-float (compiler_rt) or hardware
/// implementation could round differently: NaN sign/payload, subnormal rounding, conversions.
fn floatCases(out: *std.Io.Writer, comptime T: type) !void {
    const B = Bits(T);
    const zero = rt(T, 0.0);
    const one = rt(T, 1.0);
    const three = rt(T, 3.0);
    const half = rt(T, 0.5);
    const nan = rt(T, std.math.nan(T));
    const tiny: T = @bitCast(rt(B, 1)); // smallest subnormal (f80: explicit integer bit clear)
    const min_normal = rt(T, std.math.floatMin(T));
    const e = rt(T, std.math.floatEps(T));
    try fop(out, T, "1/3", one / three);
    try fop(out, T, "sqrt(2)", @sqrt(rt(T, 2.0)));
    try fop(out, T, "0/0", zero / zero);
    try fop(out, T, "nan+1", nan + one);
    try fop(out, T, "-nan", -nan);
    try fop(out, T, "tiny*0.5", tiny * half);
    try fop(out, T, "tiny*1.5", tiny * rt(T, 1.5));
    try fop(out, T, "min_normal*0.5", min_normal * half);
    try fop(out, T, "min_normal-tiny", min_normal - tiny);
    try fop(out, T, "max*2", rt(T, std.math.floatMax(T)) * rt(T, 2.0));
    try fop(out, T, "mulAdd(1+e,1-e,-1)", @mulAdd(T, one + e, one - e, -one));
    try fop(out, T, "f64(1/3)", @as(f64, @floatCast(one / three)));
    try fop(out, T, "f64(tiny)", @as(f64, @floatCast(tiny)));
    try fop(out, T, "of(f64.tiny)", @as(T, @floatCast(rt(f64, std.math.floatTrueMin(f64)))));
    try fop(out, T, "of(u128.max)", @as(T, @floatFromInt(rt(u128, std.math.maxInt(u128)))));
    try fop(out, T, "u64(1e19)", @as(u64, @intFromFloat(rt(T, 1e19))));
    try fop(out, T, "isnan(0/0)", std.math.isNan(zero / zero));
}

fn probeF80(out: *std.Io.Writer) !void {
    // x87 encodings that IEEE formats do not have (exponent, integer bit, fraction): x87
    // hardware treats the first three as NaN, a soft-float implementation need not.
    const cases = [_]struct { name: []const u8, b: u80 }{
        .{ .name = "unnormal(e=1,i=0)", .b = 0x0001_0000000000000001 },
        .{ .name = "pseudo-inf", .b = 0x7fff_0000000000000000 },
        .{ .name = "pseudo-nan", .b = 0x7fff_4000000000000000 },
        .{ .name = "pseudo-denormal", .b = 0x0000_8000000000000000 },
    };
    for (cases) |c| {
        const x: f80 = @bitCast(rt(u80, c.b));
        try out.print("fop f80 {s}+0 ", .{c.name});
        try hex(out, f80, x + rt(f80, 0.0));
        try out.print("\nfop f80 isnan({s}) {}\n", .{ c.name, x != x });
    }
}

fn raw(out: *std.Io.Writer, bytes: []const u8) !void {
    try out.print(" ", .{});
    var i = bytes.len;
    while (i > 0) : (i -= 1) try out.print("{x:0>2}", .{bytes[i - 1]});
}

/// `atomic <type> <size> <align> pad<byte> <cell> <won> <lost> <added> <swapped> <loaded> <cell>`:
/// the cell's bytes start as `pad`, then a plain store writes `max - 1` and the cell's raw bytes
/// (most significant first, padding included) print; then cmpxchg(max - 1 -> max) (`won`:
/// true if it succeeded), cmpxchg(0 -> 1) (fails, previous value), fetch-add 2, xchg 0x5a,
/// load, and the raw bytes again. Natural alignment is the atomicity premise. For a width
/// with padding (`u24`, `u40`) the outcome of the first cmpxchg depends on the padding bytes.
fn atomic(out: *std.Io.Writer, comptime T: type, comptime pad: u8) !void {
    const max = std.math.maxInt(T);
    var storage: [@sizeOf(T)]u8 align(@alignOf(T)) = @splat(rt(u8, pad));
    const cell: *T = @ptrCast(&storage);
    cell.* = rt(T, max - 1);
    const volatile_storage: *volatile [@sizeOf(T)]u8 = &storage;
    const before = volatile_storage.*;
    const won = @cmpxchgStrong(T, cell, max - 1, rt(T, max), .seq_cst, .seq_cst);
    const lost = @cmpxchgStrong(T, cell, 0, rt(T, 1), .seq_cst, .seq_cst);
    const added = @atomicRmw(T, cell, .Add, rt(T, 2), .seq_cst);
    const swapped = @atomicRmw(T, cell, .Xchg, rt(T, 0x5a), .acq_rel);
    const loaded = @atomicLoad(T, cell, .acquire);
    const after = volatile_storage.*;
    try out.print("atomic {s} {d} {d} pad{x:0>2}", .{ @typeName(T), @sizeOf(T), @alignOf(T), pad });
    try raw(out, &before);
    try out.print(" {}", .{won == null});
    inline for (.{ lost.?, added, swapped, loaded }) |x| {
        try out.print(" ", .{});
        try hex(out, T, x);
    }
    try raw(out, &after);
    try out.print("\n", .{});
}

pub fn main() !void {
    var buffer: [8192]u8 = undefined;
    var writer = compat.stdoutWriter(&buffer);
    const out = &writer.interface;
    try out.print("meta arch {s}\nmeta os {s}\nmeta abi {s}\nmeta cpu {s}\n", .{
        @tagName(builtin.cpu.arch), @tagName(builtin.os.tag), @tagName(builtin.abi), builtin.cpu.model.name,
    });
    try out.print("meta backend {s}\nmeta mode {s}\nmeta zig {s}\nmeta endian {s}\n", .{
        @tagName(builtin.zig_backend), @tagName(builtin.mode), builtin.zig_version_string,
        @tagName(builtin.cpu.arch.endian()),
    });
    // The features that decide how floats and atomics lower (LSE: single-instruction atomics
    // and CASP for 128 bits; otherwise LL/SC loops or outlined helpers).
    inline for (.{ "fp_armv8", "neon", "fullfp16", "lse", "lse2", "outline_atomics", "rcpc" }) |name| {
        const enabled = std.Target.aarch64.featureSetHas(builtin.cpu.features, @field(std.Target.aarch64.Feature, name));
        try out.print("feature {s} {d}\n", .{ name, @intFromBool(enabled) });
    }

    try int(out, u7, 0x55);
    try int(out, i7, -2);
    try int(out, u24, 0xabcdef);
    try int(out, i24, -0x123456);
    try int(out, u40, 0xaabbccddee);
    try int(out, i40, -1);
    try int(out, u65, (1 << 64) | 0x0123456789abcdef);
    try int(out, u96, 0x0123456789abcdef_fedcba98);
    try int(out, u128, 0x0123456789abcdef_fedcba9876543210);
    try int(out, i128, -0x0123456789abcdef_fedcba9876543210);
    try intop(out, u24, "max+%2", rt(u24, 0xffffff) +% rt(u24, 2));
    try intop(out, i7, "min-%1", rt(i7, -64) -% rt(i7, 1));
    try intop(out, i7, "min*%-1", rt(i7, -64) *% rt(i7, -1));
    try intop(out, u40, "mul_wrap", rt(u40, 0xaabbccddee) *% rt(u40, 0x1122334455));
    try intop(out, u128, "mul_wrap", rt(u128, 0x0123456789abcdef_fedcba9876543210) *% rt(u128, 0xfedcba9876543210_0123456789abcdef));
    try intop(out, u128, "div", rt(u128, std.math.maxInt(u128)) / rt(u128, 0x1_0000000000000003));
    try intop(out, i128, "rem", @rem(rt(i128, std.math.minInt(i128) + 7), rt(i128, -0x10000000000000001)));
    try intop(out, i128, "shr", rt(i128, std.math.minInt(i128) + 0x55) >> @intCast(rt(u7, 100)));
    try intop(out, u65, "add_wrap", rt(u65, std.math.maxInt(u65)) +% rt(u65, 3));

    try float(out, "f16", f16);
    try float(out, "f32", f32);
    try float(out, "f64", f64);
    try float(out, "f80", f80);
    try float(out, "f128", f128);
    try float(out, "c_longdouble", c_longdouble);
    try floatCases(out, f80);
    try probeF80(out);
    try floatCases(out, f128);

    inline for (.{ u8, u16, u24, u32, u40, u64, u128 }) |T| {
        try atomic(out, T, 0x00);
        try atomic(out, T, 0xff);
    }
    try out.print("sync cache_line {d}\n", .{std.atomic.cache_line});
    try out.flush();
}
