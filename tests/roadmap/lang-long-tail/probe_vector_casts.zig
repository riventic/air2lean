//! Native probe of `vector_casts.zig` (stock Zig 0.14.1-0.17.0). Each line is
//! `<function> <case> <result>`: an integer in decimal, a vector or array as its items in
//! decimal separated by `,`, or a `bool`. `ModelVectorCasts.lean` prints the same lines from the
//! translation.
const std = @import("std");
const vc = @import("vector_casts.zig");

fn print(comptime fmt: []const u8, args: anytype) void {
    std.debug.print(fmt, args);
}

fn items(name: []const u8, case: u32, xs: anytype) void {
    print("{s} {d} ", .{ name, case });
    const n = @typeInfo(@TypeOf(xs)).@"array".len;
    inline for (0..n) |i| {
        if (i != 0) print(",", .{});
        print("{d}", .{@as(u64, xs[i])});
    }
    print("\n", .{});
}

fn lanes(name: []const u8, case: u32, v: anytype) void {
    const n = @typeInfo(@TypeOf(v)).vector.len;
    var arr: [n]u64 = undefined;
    inline for (0..n) |i| arr[i] = if (@TypeOf(v[i]) == bool) @intFromBool(v[i]) else v[i];
    items(name, case, arr);
}

// `noinline` and runtime operands: the casts are runtime `bitcast`s, not comptime folds.
noinline fn id(comptime T: type, v: T) T {
    return v;
}

pub fn main() void {
    var a: [16]u8 = undefined;
    var b: [16]u8 = undefined;
    for (&a, &b, 0..) |*x, *y, i| {
        x.* = @intCast(i * 7 % 256);
        y.* = x.*;
    }
    print("eqlChunk 0 {}\n", .{vc.eqlChunk(id([16]u8, a), id([16]u8, b))});
    b[15] ^= 1;
    print("eqlChunk 1 {}\n", .{vc.eqlChunk(id([16]u8, a), id([16]u8, b))});
    var s: [40]u8 = undefined;
    var t: [40]u8 = undefined;
    for (&s, &t, 0..) |*x, *y, i| {
        x.* = @intCast(i * 13 % 256);
        y.* = x.*;
    }
    print("stdEql 0 {}\n", .{vc.stdEql(&s, &t)});
    t[33] +%= 1;
    print("stdEql 1 {}\n", .{vc.stdEql(&s, &t)});
    t[33] -%= 1;
    t[0] +%= 1;
    print("stdEql 2 {}\n", .{vc.stdEql(&s, &t)});

    lanes("bytesToLanes", 0, vc.bytesToLanes(id([4]u8, .{ 1, 2, 3, 250 })));
    items("lanesToBytes", 0, vc.lanesToBytes(id(@Vector(4, u8), .{ 9, 8, 7, 255 })));
    lanes("u24ItemToLane", 0, vc.u24ItemToLane(id([1]u24, .{0xabcdef})));
    items("u24LaneToItem", 0, vc.u24LaneToItem(id(@Vector(1, u24), .{0x123456})));
    lanes("boolItemToLane", 0, vc.boolItemToLane(id([1]bool, .{true})));
    print("boolLanesToByte 0 {d}\n", .{vc.boolLanesToByte(id(@Vector(8, bool), .{ true, false, true, true, false, false, false, true }))});
    print("lanesToWord 0 {d}\n", .{vc.lanesToWord(id(@Vector(4, u8), .{ 0x11, 0x22, 0x33, 0x44 }))});
    lanes("wordToLanes", 0, vc.wordToLanes(id(u32, 0xdeadbeef)));
    lanes("bytesToHalves", 0, vc.bytesToHalves(id([4]u8, .{ 0x01, 0x02, 0x03, 0x04 })));
    items("halvesToBytes", 0, vc.halvesToBytes(id(@Vector(2, u16), .{ 0xbeef, 0x1234 })));
    print("packedLanesToInt 0 {d}\n", .{vc.packedLanesToInt(id(@Vector(3, u3), .{ 1, 6, 5 }))});
    lanes("intToPackedLanes", 0, vc.intToPackedLanes(id(u9, 0b101_110_001)));
}
