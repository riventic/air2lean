//! F02 probe (docs/research/F02.md): f128 transcendentals are computed through f64 on Zig 0.15.2.
//! Recorded on aarch64-macos: @exp(f128 1000) = inf; @log(1+2^-60)-2^-60 = -8.67e-19 (exact -2^-121).
const std = @import("std");
pub fn main() void {
    var v: f128 = 1000.0;
    _ = &v;
    const r = @exp(v);
    std.debug.print("f128 @exp(1000) = {d} (isInf {}) ; true value ~ 1.97e434 is finite in f128\n", .{ @as(f64, @floatCast(r)), std.math.isInf(r) });
    var w: f128 = 1.0 + 0x1p-60;
    _ = &w;
    const l = @log(w);
    const d: f128 = l - 0x1p-60;
    std.debug.print("f128 @log(1+2^-60) - 2^-60 = {e} (f128 exact is about -2^-121 = -3.8e-37; f64-based gives {e})\n", .{ @as(f64, @floatCast(d)), @as(f64, @floatCast(d)) });
}
