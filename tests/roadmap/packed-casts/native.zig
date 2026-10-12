//! Prints each case of `packed_casts.zig` (and of `logical017.zig` on Zig 0.17, of
//! `vector_fields.zig` and `auto_items.zig` on 0.14.1/0.15.2) as one
//! line `name: value` on stderr, values in hex; `Model.lean` prints the model's lines for the
//! same cases.
//! A float is printed as its bits. Run by `check.sh --native`.
const std = @import("std");
const builtin = @import("builtin");
const pc = @import("packed_casts.zig");
const logical = builtin.zig_version.minor >= 17;
const l17 = if (logical) @import("logical017.zig") else struct {};
/// Vector fields of packed structs exist in 0.14.1 and 0.15.2 only.
const vector_fields = builtin.zig_version.minor <= 15;
const vf = if (vector_fields) @import("vector_fields.zig") else struct {};
const ai = if (vector_fields) @import("auto_items.zig") else struct {};

/// `uN` of `bits` bits, for the widths here (`std.meta.Int` is gone in 0.17).
fn Uint(comptime bits: u16) type {
    return switch (bits) {
        2 => u2,
        4 => u4,
        6 => u6,
        8 => u8,
        16 => u16,
        18 => u18,
        24 => u24,
        32 => u32,
        40 => u40,
        64 => u64,
        else => @compileError("add the width"),
    };
}

/// The output goes to stderr (`std.debug.print`, the same API in every version).
fn line(name: []const u8, comptime fmt: []const u8, args: anytype) void {
    std.debug.print("{s}: " ++ fmt ++ "\n", .{name} ++ args);
}

fn hex(name: []const u8, v: anytype) void {
    line(name, "0x{x}", .{@as(Uint(@bitSizeOf(@TypeOf(v))), @bitCast(v))});
}

fn hexs(name: []const u8, a: anytype) void {
    var buf: [256]u8 = undefined;
    var n: usize = 0;
    for (a, 0..) |v, i| {
        const I = Uint(@bitSizeOf(@TypeOf(v)));
        const s = std.fmt.bufPrint(buf[n..], "{s}0x{x}", .{ if (i == 0) "" else " ", @as(I, @bitCast(v)) }) catch unreachable;
        n += s.len;
    }
    line(name, "[{s}]", .{buf[0..n]});
}

fn vec(comptime n: usize, T: type, v: @Vector(n, T)) [n]T {
    return v;
}

pub fn main() void {
    hex("setUnion", pc.setUnion());
    hex("unionKeepsA", pc.unionKeepsA());
    hex("unionHalfHi", pc.unionHalfHi());
    hex("unionFloatView", pc.unionFloatView());
    hex("setFloat", pc.setFloat());
    hex("floatKeepsNeighbours", pc.floatKeepsNeighbours());
    hex("floatInPlace", pc.floatInPlace(1.25));
    hex("wideFloat", pc.wideFloat(3.5));
    hex("wToInt", pc.wToInt(@bitCast(@as(u64, 0x0000_0E5F_3F80_0000))));
    hex("rToInt", pc.rToInt(@bitCast(@as(u40, 0x5A_3C00_1234))));
    hex("intToR", pc.rToInt(pc.intToR(0x12_3456_7890)));
    hex("makeR", pc.makeR(0xA, 1.0));
    hex("floatField", pc.floatField(-0.5));
    hex("floatFieldNaN", pc.floatField(std.math.nan(f16)));
    hexs("uToBytes", pc.uToBytes(@bitCast(@as(u16, 0xABCD))));
    hex("bytesToU", pc.bytesToU(.{ 0x34, 0x12 }));
    hex("uToHalf", pc.uToHalf(@bitCast(@as(u16, 0xBEEF))));
    hex("halfToF16", pc.halfToF16(.{ .lo = 0x00, .hi = 0x3C }));
    hex("f16ToU", pc.f16ToU(-1.0));
    hex("floatsToInt", pc.floatsToInt(.{ 1.0, -2.0 }));
    hexs("intToFloats", pc.intToFloats(0x4040_0000_BF80_0000));
    hex("vecToInt", pc.vecToInt(.{ 0.5, 4.0 }));
    hexs("intToVec", vec(2, f32, pc.intToVec(0x3F80_0000_C000_0000)));
    if (vector_fields) {
        hex("setVector", vf.setVector(1, 2, 3));
        hex("lane1", vf.lane1(0x321A));
        hex("laneSum", vf.laneSum(0x321A));
        hex("structsToInt", ai.structsToInt(.{ .{ .a = 1, .b = 2 }, .{ .a = 3, .b = 4 } }));
        hex("structB1", ai.structB1(0x0004_0003_0002_0001));
        hex("unionPayload1", ai.unionPayload1(0x0000_BEEF_0001_1234));
        hex("unionsToInt", ai.unionsToInt(.{ .{ .a = 0x1234 }, .{ .b = 0x56 } }));
    }
    if (logical) {
        hex("nestedToInt", l17.nestedToInt(.{ .{ 1, 2, 3 }, .{ 4, 5, 6 } }));
        const nested = l17.intToNested(0xFEDCBA);
        hexs("intToNested0", nested[0]);
        hexs("intToNested1", nested[1]);
        hex("modesToInt", l17.modesToInt(.{ .low, .high, .off, .low }));
        hexs("intToModes", l17.intToModes(0x26));
        hex("nibsToInt", l17.nibsToInt(.{ .{ .a = 1, .m = .high, .b = 3 }, .{ .a = 2, .m = .low, .b = 0 }, .{ .a = 3, .m = .off, .b = 1 } }));
        hexs("intToNibs", l17.intToNibs(0x2_1A5B));
        hex("unionsToInt", l17.unionsToInt(.{ .{ .i = 0x1234 }, .{ .h = 1.0 } }));
        hexs("uToNibbles", l17.uToNibbles(.{ .i = 0xC0DE }));
        hex("nibblesToU", l17.nibblesToU(.{ 0xD, 0xE, 0xA, 0xF }));
        hexs("halvesToVec", vec(4, u8, l17.halvesToVec(.{ 1.0, -2.0 })));
        hexs("vecToHalves", l17.vecToHalves(.{ 0.5, 2.0 }));
        const fl = l17.floatsToNested(.{ 1.0, -0.0 });
        hexs("floatsToNested0", fl[0]);
        hexs("floatsToNested1", fl[1]);
    }
}
