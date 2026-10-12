//! F02 probe: platform libm (`@sin` etc. with libc linked) vs Zig's compiler_rt, same binary.
const std = @import("std");
const crt = @import("crt");
fn ulps(comptime T: type, a: T, b: T) u64 {
    const U = if (T == f32) u32 else u64;
    if (std.math.isNan(a) and std.math.isNan(b)) return 0;
    const ia: U = @bitCast(a);
    const ib: U = @bitCast(b);
    return if (ia > ib) ia - ib else ib - ia;
}
fn run(comptime T: type, comptime name: []const u8, comptime lo: T, comptime hi: T, f: anytype, g: anytype) void {
    var prng = std.Random.DefaultPrng.init(42);
    const r = prng.random();
    var diff: u32 = 0; var maxu: u64 = 0; var ex: T = 0;
    const n = 200000;
    for (0..n) |_| {
        const x: T = lo + (hi - lo) * r.float(T);
        const u = ulps(T, f(x), g(x));
        if (u != 0) diff += 1;
        if (u > maxu) { maxu = u; ex = x; }
    }
    std.debug.print("{s}: differing {d}/{d} max_ulp_between_impls {d} at {e}\n", .{ name, diff, n, maxu, ex });
}
fn sin64(x: f64) f64 { return @sin(x); }
fn exp64(x: f64) f64 { return @exp(x); }
fn log64(x: f64) f64 { return @log(x); }
fn exp264(x: f64) f64 { return @exp2(x); }
fn sin32(x: f32) f32 { return @sin(x); }
fn exp32(x: f32) f32 { return @exp(x); }
fn log32(x: f32) f32 { return @log(x); }
pub fn main() void {
    run(f64, "sin f64 [-100,100]", -100, 100, sin64, crt.sin.sin);
    run(f64, "exp f64 [-20,20]", -20, 20, exp64, crt.exp.exp);
    run(f64, "log f64 (0,1e6]", 1e-9, 1e6, log64, crt.log.log);
    run(f64, "exp2 f64 [-20,20]", -20, 20, exp264, crt.exp2.exp2);
    run(f32, "sin f32 [-100,100]", -100, 100, sin32, crt.sin.sinf);
    run(f32, "exp f32 [-20,20]", -20, 20, exp32, crt.exp.expf);
    run(f32, "log f32 (0,1e6]", 1e-9, 1e6, log32, crt.log.logf);
}
