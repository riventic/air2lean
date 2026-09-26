//! Prints the result bits of the float cases that Zig leaves to the target (docs/floats.md
//! §Semantics). CI runs it on the reference target and compares with `expected.txt`.
//! Build: `zig build-exe -OReleaseSafe -mcpu=baseline tests/floatprobe/probe.zig`.
const std = @import("std");

/// Hides `x` from the optimizer, so that each case runs on the target, not in LLVM's
/// constant folder.
fn rt(comptime T: type, x: T) T {
    var v: T = x;
    const p: *volatile T = &v;
    return p.*;
}

fn bits(comptime T: type, x: T) std.meta.Int(.unsigned, @bitSizeOf(T)) {
    return @bitCast(x);
}

fn line(out: *std.Io.Writer, comptime T: type, name: []const u8, x: T) !void {
    const w = comptime @bitSizeOf(T) / 4;
    try out.print("{s} {s} {x:0>" ++ std.fmt.comptimePrint("{d}", .{w}) ++ "}\n", .{ @typeName(T), name, bits(T, x) });
}

fn probeType(out: *std.Io.Writer, comptime T: type) !void {
    const pz = rt(T, 0.0);
    const nz = rt(T, -0.0);
    const one = rt(T, 1.0);
    const three = rt(T, 3.0);
    const nan = rt(T, std.math.nan(T));
    const inf = rt(T, std.math.inf(T));

    try line(out, T, "min(+0,-0)", @min(pz, nz));
    try line(out, T, "min(-0,+0)", @min(nz, pz));
    try line(out, T, "max(+0,-0)", @max(pz, nz));
    try line(out, T, "max(-0,+0)", @max(nz, pz));
    try line(out, T, "min(nan,1)", @min(nan, one));
    try line(out, T, "min(1,nan)", @min(one, nan));
    try line(out, T, "max(nan,1)", @max(nan, one));
    try line(out, T, "0/0", pz / pz);
    try line(out, T, "inf-inf", inf - inf);
    try line(out, T, "sqrt(-1)", @sqrt(-one));
    try line(out, T, "nan+1", nan + one);
    try line(out, T, "-nan", -nan);
    try line(out, T, "round(2.5)", @round(rt(T, 2.5)));
    try line(out, T, "round(-2.5)", @round(rt(T, -2.5)));
    try line(out, T, "round(0.5)", @round(rt(T, 0.5)));
    try line(out, T, "rem(-1,3)", @rem(-one, three));
    try line(out, T, "mod(-1,3)", @mod(-one, three));
    try line(out, T, "mod(1,-3)", @mod(one, -three));
    try line(out, T, "mod(-0,3)", @mod(nz, three));
    try line(out, T, "mod(-3,3)", @mod(-three, three));
    try line(out, T, "rem(-3,3)", @rem(-three, three));
    try line(out, T, "sqrt(2)", @sqrt(rt(T, 2.0)));
    try line(out, T, "sqrt(3)", @sqrt(three));
    try line(out, T, "divTrunc(-7,2)", @divTrunc(rt(T, -7.0), rt(T, 2.0)));
    try line(out, T, "divFloor(-7,2)", @divFloor(rt(T, -7.0), rt(T, 2.0)));
    // A case where fma rounds once but a*b+c rounds twice: (1+e)(1-e) - 1 = -e^2.
    const e = rt(T, std.math.floatEps(T));
    try line(out, T, "mulAdd(1+e,1-e,-1)", @mulAdd(T, one + e, one - e, -one));
    // f16 via f32 double rounding: a product that lands just above a half-ulp tie.
    try line(out, T, "mulAdd(3,1/3,-1)", @mulAdd(T, three, rt(T, 1.0) / three, -one));
}

fn probeF80(out: *std.Io.Writer) !void {
    // x87 encodings that IEEE formats do not have (exponent, integer bit, fraction).
    const cases = [_]struct { name: []const u8, b: u80 }{
        .{ .name = "unnormal(e=1,i=0)", .b = 0x0001_0000000000000001 },
        .{ .name = "pseudo-inf", .b = 0x7fff_0000000000000000 },
        .{ .name = "pseudo-nan", .b = 0x7fff_4000000000000000 },
        .{ .name = "pseudo-denormal", .b = 0x0000_8000000000000000 },
    };
    for (cases) |c| {
        const x: f80 = @bitCast(rt(u80, c.b));
        try line(out, f80, c.name, x + rt(f80, 0.0));
        try out.print("f80 {s} isnan={}\n", .{ c.name, x != x });
    }
}

pub fn main() !void {
    var buf: [4096]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    const out = &w.interface;
    inline for (.{ f16, f32, f64, f80, f128 }) |T| try probeType(out, T);
    try probeF80(out);
    try out.flush();
}
