// TEMPORARY (F0 libm spike): the harness side, @sin etc. inline in an executable.
// Prints "<op> <input bits> <output bits>" in hex.
const std = @import("std");
fn rt(comptime T: type, x: T) T {
    var v: T = x;
    const p: *volatile T = &v;
    return p.*;
}
fn U(comptime T: type) type {
    return std.meta.Int(.unsigned, @bitSizeOf(T));
}
fn line(out: *std.Io.Writer, comptime T: type, op: []const u8, x: T, y: T) !void {
    try out.print("{s} {x} {x}\n", .{ op, @as(U(T), @bitCast(x)), @as(U(T), @bitCast(y)) });
}
pub fn main() !void {
    var buf: [4096]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const out = &w.interface;
    var rng = std.Random.DefaultPrng.init(42);
    const r = rng.random();
    for (0..1000) |_| {
        const x: f64 = (r.float(f64) - 0.5) * 200.0;
        const x32: f32 = @floatCast(@abs(x));
        const x80: f80 = @floatCast(x);
        const x128: f128 = @floatCast(x);
        try line(out, f64, "sin64", x, @sin(rt(f64, x)));
        try line(out, f64, "exp64", x / 100.0, @exp(rt(f64, x / 100.0)));
        try line(out, f32, "log32", x32, @log(rt(f32, x32)));
        try line(out, f80, "sin80", x80, @sin(rt(f80, x80)));
        try line(out, f128, "sin128", x128, @sin(rt(f128, x128)));
    }
    try out.flush();
}
