//! Native side of the `@divCeil` differential (`check.sh`), built with a stock Zig 0.17.0 in
//! ReleaseSafe. `native`: one `fn a b result` line per line of `inputs.txt`, `panic` where the
//! inputs reach a safety check (the process would stop there). `native --one fn a b`: call that
//! one function, so a safety check ends the process with Zig's panic message.
const std = @import("std");
const d = @import("divceil");

fn panics(comptime T: type, a: T, b: T) bool {
    if (b == 0) return true;
    return @typeInfo(T).int.signedness == .signed and a == std.math.minInt(T) and b == -1;
}

fn eval(name: []const u8, a_text: []const u8, b_text: []const u8, check: bool, out: *std.Io.Writer) !void {
    inline for (.{
        .{ "divCeilI8", i8, d.divCeilI8 },   .{ "divCeilU8", u8, d.divCeilU8 },
        .{ "divCeilI32", i32, d.divCeilI32 }, .{ "divCeilU32", u32, d.divCeilU32 },
        .{ "divCeilI64", i64, d.divCeilI64 }, .{ "divCeilU64", u64, d.divCeilU64 },
        .{ "divCeilI13", i13, d.divCeilI13 },
    }) |e| {
        if (std.mem.eql(u8, name, e[0])) {
            const T = e[1];
            var a: T = try std.fmt.parseInt(T, a_text, 10);
            var b: T = try std.fmt.parseInt(T, b_text, 10);
            if (check and panics(T, a, b)) {
                try out.print("{s} {d} {d} panic\n", .{ name, a, b });
            } else {
                // Through volatile copies, so the call is a runtime `div_ceil`.
                const pa: *volatile T = &a;
                const pb: *volatile T = &b;
                try out.print("{s} {d} {d} {d}\n", .{ name, a, b, e[2](pa.*, pb.*) });
            }
            return;
        }
    }
    return error.UnknownFunction;
}

pub fn main(init: std.process.Init) !void {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    var buffer: [4096]u8 = undefined;
    var writer = std.Io.File.stdout().writer(init.io, &buffer);
    const out = &writer.interface;
    if (args.len == 5 and std.mem.eql(u8, args[1], "--one")) {
        try out.print("calling {s} {s} {s}\n", .{ args[2], args[3], args[4] });
        try out.flush();
        try eval(args[2], args[3], args[4], false, out);
    } else {
        var lines = std.mem.tokenizeScalar(u8, @embedFile("inputs.txt"), '\n');
        while (lines.next()) |line| {
            var fields = std.mem.tokenizeScalar(u8, line, ' ');
            const name = fields.next().?;
            try eval(name, fields.next().?, fields.next().?, true, out);
        }
    }
    try out.flush();
}
