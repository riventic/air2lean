const std = @import("std");
const builtin = @import("builtin");
fn bits(comptime T: type, x: T) std.meta.Int(.unsigned, @bitSizeOf(T)) {
    return @bitCast(x);
}
fn pr(name: []const u8, comptime T: type, x: T) void {
    std.debug.print("{s} {x}\n", .{ name, bits(T, x) });
}
fn f(comptime T: type, v: std.meta.Int(.unsigned, @bitSizeOf(T))) T {
    return @bitCast(v);
}
noinline fn id(comptime T: type, x: T) T {
    var y: T = x;
    const p: *volatile T = &y;
    return p.*;
}
pub fn main() void {
    std.debug.print("libc {}\n", .{builtin.link_libc});
    // f16 fma: fused one rounding = 3e01; via f32 = 3e02
    pr("f16 fma", f16, @mulAdd(f16, id(f16, f(f16, 0x3e00)), id(f16, f(f16, 0x3c01)), id(f16, f(f16, 0x8001))));
    pr("f16 0/0", f16, id(f16, 0.0) / id(f16, 0.0));
    pr("f32 0/0", f32, id(f32, 0.0) / id(f32, 0.0));
    pr("f64 0/0", f64, id(f64, 0.0) / id(f64, 0.0));
    pr("f80 0/0", f80, id(f80, 0.0) / id(f80, 0.0));
    pr("f128 0/0", f128, id(f128, 0.0) / id(f128, 0.0));
    pr("f32 nanpay+1", f32, id(f32, f(f32, 0xff812345)) + id(f32, 1.0));
    pr("f64 nanpay+1", f64, id(f64, f(f64, 0xfff0000000012345)) + id(f64, 1.0));
    pr("f16 nanpay+1", f16, id(f16, f(f16, 0xfd23)) + id(f16, 1.0));
    pr("f128 nanpay+1", f128, id(f128, f(f128, 0xffff0000000000000000000000012345)) + id(f128, 1.0));
    pr("f80 nanpay+1", f80, id(f80, f(f80, 0xffff8000000000012345)) + id(f80, 1.0));
    pr("f64 sqrt(-1)", f64, @sqrt(id(f64, -1.0)));
    pr("f128 sqrt(-1)", f128, @sqrt(id(f128, -1.0)));
    pr("f128 sqrt(2)", f128, @sqrt(id(f128, 2.0)));
    pr("f128 sqrt(3)", f128, @sqrt(id(f128, 3.0)));
    pr("f80 sqrt(2)", f80, @sqrt(id(f80, 2.0)));
    // fmaq Dekker NaN: fma(0.25,0.25,2^16383)
    pr("f128 fma big", f128, @mulAdd(f128, id(f128, 0.25), id(f128, 0.25), id(f128, f(f128, 0x7ffe0000000000000000000000000000))));
    pr("f64 fma big", f64, @mulAdd(f64, id(f64, 0.25), id(f64, 0.25), id(f64, f(f64, 0x7fe0000000000000))));
    pr("f128 fma 1+e", f128, @mulAdd(f128, id(f128, 1.0 + std.math.floatEps(f128)), id(f128, 1.0 - std.math.floatEps(f128)), id(f128, -1.0)));
    pr("f128 sin1", f128, @sin(id(f128, 1.0)));
    pr("f128 exp1", f128, @exp(id(f128, 1.0)));
    pr("f128 floor", f128, @floor(id(f128, -2.5)));
    pr("f128 rem", f128, @rem(id(f128, 7.5), id(f128, 2.0)));
    pr("f128 min snan", f128, @min(id(f128, f(f128, 0x7fff4000000000000000000000000000)), id(f128, 1.0)));
    pr("f64 min snan", f64, @min(id(f64, f(f64, 0x7ff4000000000000)), id(f64, 1.0)));
    pr("f128 min qnan", f128, @min(id(f128, f(f128, 0x7fff8000000000000000000000000001)), id(f128, 1.0)));
    pr("f128 min 0", f128, @min(id(f128, 0.0), id(f128, -0.0)));
    pr("f64 min 0", f64, @min(id(f64, 0.0), id(f64, -0.0)));
    pr("f64 max 0", f64, @max(id(f64, -0.0), id(f64, 0.0)));
    pr("f32 min 0", f32, @min(id(f32, 0.0), id(f32, -0.0)));
    pr("f32 max 0b", f32, @max(id(f32, 0.0), id(f32, -0.0)));
    pr("f16 min 0", f16, @min(id(f16, 0.0), id(f16, -0.0)));
    pr("f80 min 0", f80, @min(id(f80, 0.0), id(f80, -0.0)));
    pr("f128 max 0", f128, @max(id(f128, -0.0), id(f128, 0.0)));
    pr("f128->f80 lownan", f80, @floatCast(id(f128, f(f128, 0x7fff0000000000000000000000000001))));
    pr("f64->f32 nanpay", f32, @floatCast(id(f64, f(f64, 0x7ff8000000012345))));
    pr("f32->f64 snan", f64, @floatCast(id(f32, f(f32, 0x7f812345))));
    std.debug.print("ld bits {}\n", .{@bitSizeOf(c_longdouble)});
}
