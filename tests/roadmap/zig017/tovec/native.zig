//! Native side of the `array_to_vector` differential (`check.sh`), built with a stock Zig 0.17.1
//! in ReleaseSafe. Each line `fn x0 … x(n-1)` of `inputs.txt` (an integer item in decimal, a
//! `bool` as 0/1, a float as its bit pattern) becomes the function's array, sentinel included,
//! and the function's vector is printed as `fn y0 … y(n-1)` in the same encoding.
const std = @import("std");
const t = @import("tovec");

fn Bits(comptime T: type) type {
    return @Int(.unsigned, @bitSizeOf(T));
}

fn parse(comptime T: type, text: []const u8) !T {
    return switch (@typeInfo(T)) {
        .bool => (try std.fmt.parseInt(u1, text, 10)) == 1,
        .float => @bitCast(try std.fmt.parseInt(Bits(T), text, 10)),
        else => try std.fmt.parseInt(T, text, 10),
    };
}

fn show(x: anytype, out: *std.Io.Writer) !void {
    const T = @TypeOf(x);
    switch (@typeInfo(T)) {
        .bool => try out.print(" {d}", .{@intFromBool(x)}),
        .float => try out.print(" {d}", .{@as(Bits(T), @bitCast(x))}),
        else => try out.print(" {d}", .{x}),
    }
}

fn eval(name: []const u8, items: *std.mem.TokenIterator(u8, .scalar), out: *std.Io.Writer) !void {
    inline for (.{
        .{ "toVecU8", t.toVecU8 },     .{ "toVecI16", t.toVecI16 },   .{ "toVecU24", t.toVecU24 },
        .{ "toVecI32", t.toVecI32 },   .{ "toVecU64", t.toVecU64 },   .{ "toVecI128", t.toVecI128 },
        .{ "toVecU1", t.toVecU1 },     .{ "toVecI7", t.toVecI7 },     .{ "toVecBool", t.toVecBool },
        .{ "toVecF16", t.toVecF16 },   .{ "toVecF32", t.toVecF32 },   .{ "toVecF64", t.toVecF64 },
        .{ "toVecF80", t.toVecF80 },   .{ "toVecF128", t.toVecF128 }, .{ "toVecZ8", t.toVecZ8 },
        .{ "toVecZ16", t.toVecZ16 },
    }) |e| {
        if (std.mem.eql(u8, name, e[0])) {
            const A = @typeInfo(@TypeOf(e[1])).@"fn".param_types[0].?;
            const info = @typeInfo(A).array;
            // Every item, and the sentinel of a sentinel-terminated array, from one `@splat`.
            var a: A = @splat(if (info.sentinel()) |s| s else std.mem.zeroes(info.child));
            for (0..info.len) |i| a[i] = try parse(info.child, items.next() orelse return error.Short);
            if (items.next() != null) return error.Long;
            // Through a volatile copy, so the call's operand is a runtime array.
            const pa: *volatile A = &a;
            const v = e[1](pa.*);
            try out.print("{s}", .{name});
            inline for (0..info.len) |i| try show(v[i], out);
            try out.print("\n", .{});
            return;
        }
    }
    return error.UnknownFunction;
}

pub fn main(init: std.process.Init) !void {
    var buffer: [4096]u8 = undefined;
    var writer = std.Io.File.stdout().writer(init.io, &buffer);
    const out = &writer.interface;
    var lines = std.mem.tokenizeScalar(u8, @embedFile("inputs.txt"), '\n');
    while (lines.next()) |line| {
        var fields = std.mem.tokenizeScalar(u8, line, ' ');
        try eval(fields.next().?, &fields, out);
    }
    try out.flush();
}
