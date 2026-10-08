//! L07 native probe (stock Zig 0.14.1-0.16.0): `@bitCast` of arrays, `extern` structs and
//! `extern` unions reinterprets memory, and optional pointers use address 0 for null. Each line
//! is `<case> <hex bytes of the result, little-endian>` or `<case> <value>`. `Model.lean`
//! prints the model's lines and compares them: a case whose model result is `.unspecified`
//! (it reads a padding byte) is only recorded.
const std = @import("std");

const Pair = extern struct { a: u32, b: u32 }; // no padding
const Padded = extern struct { a: u8, b: u32 }; // bytes 1..3 are padding
const Word = extern union { int: u32, bytes: [4]u8 };
const Short = extern union { a: u8, b: u32 }; // bytes 1..3 are padding of `a`

fn bytesOf(comptime T: type, v: T) [@sizeOf(T)]u8 {
    return std.mem.toBytes(v);
}

fn line(name: []const u8, bytes: []const u8) void {
    std.debug.print("{s}", .{name});
    for (bytes) |b| std.debug.print(" {x:0>2}", .{b});
    std.debug.print("\n", .{});
}

// `noinline` and runtime operands: the casts are runtime `bitcast`s, not comptime folds.
noinline fn id(comptime T: type, v: T) T {
    return v;
}

pub fn main() void {
    const b4 = id([4]u8, .{ 0x11, 0x22, 0x33, 0x44 });
    line("bytes_u32", &bytesOf(u32, @bitCast(b4)));
    line("u32_bytes", &bytesOf([4]u8, @bitCast(id(u32, 0x44332211))));
    line("pair_u64", &bytesOf(u64, @bitCast(id(Pair, .{ .a = 1, .b = 2 }))));
    line("u64_pair", &bytesOf(Pair, @bitCast(id(u64, 0x0000000200000001))));
    const p: Padded = @bitCast(id([8]u8, .{ 1, 2, 3, 4, 5, 6, 7, 8 }));
    line("bytes_padded.a", &bytesOf(u8, p.a));
    line("bytes_padded.b", &bytesOf(u32, p.b));
    line("padded_bytes", &bytesOf([8]u8, @bitCast(id(Padded, .{ .a = 1, .b = 0x05040302 }))));
    line("u24x2_u56", &bytesOf(u56, @bitCast(id([2]u24, .{ 0x112233, 0x445566 }))));
    line("u56_u24x2", &bytesOf([2]u24, @bitCast(id(u56, 0x44556600112233))));
    const w: Word = @bitCast(id(u32, 0x44332211));
    line("u32_word.bytes", &w.bytes);
    line("short_u32", &bytesOf(u32, @bitCast(id(Short, .{ .a = 0x11 }))));
    var x: u32 = 7;
    const none = id(?*u32, null);
    std.debug.print("opt_null_addr {d}\n", .{@intFromPtr(none)});
    const from0: ?*u32 = @ptrFromInt(id(usize, 0));
    std.debug.print("opt_from_zero_null {}\n", .{from0 == null});
    const some = id(?*u32, &x);
    const unwrapped: *u32 = @ptrCast(some);
    std.debug.print("opt_unwrap_same {}\n", .{@intFromPtr(unwrapped) == @intFromPtr(&x)});
    std.debug.print("opt_wrap_addr_same {}\n", .{@intFromPtr(some) == @intFromPtr(&x)});
}
