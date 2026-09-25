// TEMPORARY (F0 libm spike): calls the compiler_rt functions by their Zig names. A plain @sin
// would be a call to the symbol `sin`, and in the Lean executable the linker may bind that
// symbol to the system libm in place of compiler_rt.
const crt_sin = @import("crt").sin;
const crt_exp = @import("crt").exp;
const crt_log = @import("crt").log;

export fn air2lean_libm_sin_f64(x: u64) u64 { return @bitCast(crt_sin.sin(@bitCast(x))); }
export fn air2lean_libm_exp_f64(x: u64) u64 { return @bitCast(crt_exp.exp(@bitCast(x))); }
export fn air2lean_libm_log_f32(x: u64) u64 { return @as(u32, @bitCast(crt_log.logf(@bitCast(@as(u32, @truncate(x)))))); }
fn f80of(hi: u64, lo: u64) f80 { return @bitCast(@as(u80, @truncate((@as(u128, hi) << 64) | lo))); }
fn f128of(hi: u64, lo: u64) f128 { return @bitCast((@as(u128, hi) << 64) | lo); }
export fn air2lean_libm_sin_f80_hi(hi: u64, lo: u64) u64 { return @truncate(@as(u80, @bitCast(crt_sin.__sinx(f80of(hi, lo)))) >> 64); }
export fn air2lean_libm_sin_f80_lo(hi: u64, lo: u64) u64 { return @truncate(@as(u80, @bitCast(crt_sin.__sinx(f80of(hi, lo))))); }
export fn air2lean_libm_sin_f128_hi(hi: u64, lo: u64) u64 { return @truncate(@as(u128, @bitCast(crt_sin.sinq(f128of(hi, lo)))) >> 64); }
export fn air2lean_libm_sin_f128_lo(hi: u64, lo: u64) u64 { return @truncate(@as(u128, @bitCast(crt_sin.sinq(f128of(hi, lo))))); }
