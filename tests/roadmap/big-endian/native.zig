//! T03 native observations: every function of `big_endian.zig` on fixed inputs, one line per
//! case on stderr (`<function> <inputs> -> <result bytes or integer>`). `Diff.lean` prints the same lines
//! from the generated model; `check.sh --native` compares them per target.
const std = @import("std");
const be = @import("big_endian.zig");

fn line(name: []const u8, args: anytype, result: anytype) !void {
    std.debug.print("{s}", .{name});
    inline for (args) |a| std.debug.print(" {d}", .{a});
    std.debug.print(" ->", .{});
    const R = @TypeOf(result);
    switch (@typeInfo(R)) {
        .array => for (result) |x| std.debug.print(" {d}", .{x}),
        else => std.debug.print(" {d}", .{result}),
    }
    std.debug.print("\n", .{});
}

pub fn main() !void {
    const words = [_]u32{ 0x01020304, 0xdeadbeef, 0, 0xffffffff, 0x80000001 };
    for (words) |x| {
        try line("u32ToBytes", .{x}, be.u32ToBytes(x));
        try line("packedToBytes", .{x}, be.packedToBytes(x));
        try line("unionHalf", .{x}, be.unionHalf(x));
        for (0..4) |i| {
            try line("byteOfU32", .{ x, i }, be.byteOfU32(x, i));
            try line("unionByte", .{ x, i }, be.unionByte(x, i));
        }
        for ([_]u12{ 0, 0xabc, 0xfff }) |v| try line("setFieldBytes", .{ x, v }, be.setFieldBytes(x, v));
    }
    const quads = [_][4]u8{ .{ 1, 2, 3, 4 }, .{ 0xff, 0, 0x80, 0x7f }, .{ 0x12, 0x34, 0x56, 0x78 } };
    for (quads) |q| {
        try line("bytesToU32", .{ q[0], q[1], q[2], q[3] }, be.bytesToU32(q));
        try line("fieldFromBytes", .{ q[0], q[1], q[2], q[3] }, be.fieldFromBytes(q[0], q[1], q[2], q[3]));
        try line("u16FromStoredBytes", .{ q[0], q[1] }, be.u16FromStoredBytes(q[0], q[1]));
    }
    for ([_]i16{ 0, 1, -2, 0x1234, -32768 }) |x| try line("i16ToBytes", .{x}, be.i16ToBytes(x));
    for ([_]u64{ 0x0102030405060708, 0xfedcba9876543210 }) |x| try line("u64ToHalves", .{x}, be.u64ToHalves(x));
    for ([_]u32{ 0x3f800000, 0xc0490fdb, 0x00000001 }) |bits| {
        const x: f32 = @bitCast(bits);
        try line("f32ToBytes", .{bits}, be.f32ToBytes(x));
    }
    for ([_]u16{ 0x3c00, 0xc000, 0x7bff }) |bits| {
        const x: f16 = @bitCast(bits);
        try line("f16ToBytes", .{bits}, be.f16ToBytes(x));
    }
    const eights = [_][8]u8{ .{ 0x3f, 0xf0, 0, 0, 0, 0, 0, 0 }, .{ 1, 2, 3, 4, 5, 6, 7, 8 } };
    for (eights) |b| {
        try line("bytesToF64Bits", b, be.bytesToF64Bits(b));
    }
    for ([_]u64{ 0x3ff0000000000000, 0x400921fb54442d18 }) |bits| {
        const x: f64 = @bitCast(bits);
        for (0..8) |i| try line("byteOfF64", .{ bits, i }, be.byteOfF64(x, i));
    }
    for ([_][2]u16{ .{ 0x0102, 0x0304 }, .{ 0xffff, 0 } }) |p| {
        try line("externToBytes", .{ p[0], p[1], 0xa1b2c3d4 }, be.externToBytes(p[0], p[1], 0xa1b2c3d4));
    }
    for ([_][2]u16{ .{ 0xabc, 0xd }, .{ 0, 0xf }, .{ 0xfff, 0 } }) |p| {
        const lo: u12 = @intCast(p[0]);
        const hi: u4 = @intCast(p[1]);
        try line("packed16ToBytes", .{ lo, hi }, be.packed16ToBytes(lo, hi));
    }
}
