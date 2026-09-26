//! Static libm for the Lean side: re-exports 8 compiler_rt transcendental functions (sin, cos,
//! tan, exp, exp2, log, log2, log10) per float width, under a fixed ABI a Lean `@[extern]` opaque
//! can call (docs/floats.md).
//!
//! Calls compiler_rt by its Zig name, through the `crt` module below — never through an `extern
//! fn` of the C symbol name, which the linker could bind to the system libm instead. scripts/
//! diff.sh's build step copies Zig's own lib/zig/compiler_rt/ and adds the `crt` module's root
//! file (one `pub const <op> = @import("<op>.zig");` line per op) before building this file with:
//!   zig build-lib -static -fcompiler-rt -fPIC -OReleaseSafe -mcpu=baseline --name air2lean_libm \
//!     --dep crt -Mroot=tests/diff/libm/libm.zig -Mcrt=<generated crt root>
//!
//! ABI, one pair of functions per op x width:
//!   - f16/f32/f64: air2lean_libm_<op>_f<N>(x: u64) u64 — the float's own bits, zero-extended.
//!   - f80/f128:    air2lean_libm_<op>_f<N>_hi/_lo(hi: u64, lo: u64) u64 — the float's bits
//!                  split across two u64 halves (hi first), same split in and out.
//!
//! compiler_rt's own per-width names are not uniform (checked against Zig 0.15.2's lib/zig/
//! compiler_rt/{op}.zig for all 8 ops): `__<op>h` (f16), `<op>f` (f32), `<op>` (f64), `__<op>x`
//! (f80), `<op>q` (f128).

const std = @import("std");
const crt = @import("crt");

fn narrow(comptime T: type, x: u64, comptime f: fn (T) callconv(.c) T) u64 {
    const Bits = std.meta.Int(.unsigned, @bitSizeOf(T));
    const arg: T = @bitCast(@as(Bits, @truncate(x)));
    const rbits: Bits = @bitCast(f(arg));
    return rbits;
}

fn wideBits(comptime T: type, hi: u64, lo: u64) T {
    const Bits = std.meta.Int(.unsigned, @bitSizeOf(T));
    const combined: u128 = (@as(u128, hi) << 64) | @as(u128, lo);
    const bits: Bits = @truncate(combined);
    return @bitCast(bits);
}

fn wideHi(comptime T: type, hi: u64, lo: u64, comptime f: fn (T) callconv(.c) T) u64 {
    const Bits = std.meta.Int(.unsigned, @bitSizeOf(T));
    const rbits: Bits = @bitCast(f(wideBits(T, hi, lo)));
    return @truncate(@as(u128, rbits) >> 64);
}

fn wideLo(comptime T: type, hi: u64, lo: u64, comptime f: fn (T) callconv(.c) T) u64 {
    const Bits = std.meta.Int(.unsigned, @bitSizeOf(T));
    const rbits: Bits = @bitCast(f(wideBits(T, hi, lo)));
    return @truncate(rbits);
}

// sin
export fn air2lean_libm_sin_f16(x: u64) u64 {
    return narrow(f16, x, crt.sin.__sinh);
}
export fn air2lean_libm_sin_f32(x: u64) u64 {
    return narrow(f32, x, crt.sin.sinf);
}
export fn air2lean_libm_sin_f64(x: u64) u64 {
    return narrow(f64, x, crt.sin.sin);
}
export fn air2lean_libm_sin_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.sin.__sinx);
}
export fn air2lean_libm_sin_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.sin.__sinx);
}
export fn air2lean_libm_sin_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.sin.sinq);
}
export fn air2lean_libm_sin_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.sin.sinq);
}

// cos
export fn air2lean_libm_cos_f16(x: u64) u64 {
    return narrow(f16, x, crt.cos.__cosh);
}
export fn air2lean_libm_cos_f32(x: u64) u64 {
    return narrow(f32, x, crt.cos.cosf);
}
export fn air2lean_libm_cos_f64(x: u64) u64 {
    return narrow(f64, x, crt.cos.cos);
}
export fn air2lean_libm_cos_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.cos.__cosx);
}
export fn air2lean_libm_cos_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.cos.__cosx);
}
export fn air2lean_libm_cos_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.cos.cosq);
}
export fn air2lean_libm_cos_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.cos.cosq);
}

// tan
export fn air2lean_libm_tan_f16(x: u64) u64 {
    return narrow(f16, x, crt.tan.__tanh);
}
export fn air2lean_libm_tan_f32(x: u64) u64 {
    return narrow(f32, x, crt.tan.tanf);
}
export fn air2lean_libm_tan_f64(x: u64) u64 {
    return narrow(f64, x, crt.tan.tan);
}
export fn air2lean_libm_tan_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.tan.__tanx);
}
export fn air2lean_libm_tan_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.tan.__tanx);
}
export fn air2lean_libm_tan_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.tan.tanq);
}
export fn air2lean_libm_tan_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.tan.tanq);
}

// exp
export fn air2lean_libm_exp_f16(x: u64) u64 {
    return narrow(f16, x, crt.exp.__exph);
}
export fn air2lean_libm_exp_f32(x: u64) u64 {
    return narrow(f32, x, crt.exp.expf);
}
export fn air2lean_libm_exp_f64(x: u64) u64 {
    return narrow(f64, x, crt.exp.exp);
}
export fn air2lean_libm_exp_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.exp.__expx);
}
export fn air2lean_libm_exp_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.exp.__expx);
}
export fn air2lean_libm_exp_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.exp.expq);
}
export fn air2lean_libm_exp_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.exp.expq);
}

// exp2
export fn air2lean_libm_exp2_f16(x: u64) u64 {
    return narrow(f16, x, crt.exp2.__exp2h);
}
export fn air2lean_libm_exp2_f32(x: u64) u64 {
    return narrow(f32, x, crt.exp2.exp2f);
}
export fn air2lean_libm_exp2_f64(x: u64) u64 {
    return narrow(f64, x, crt.exp2.exp2);
}
export fn air2lean_libm_exp2_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.exp2.__exp2x);
}
export fn air2lean_libm_exp2_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.exp2.__exp2x);
}
export fn air2lean_libm_exp2_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.exp2.exp2q);
}
export fn air2lean_libm_exp2_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.exp2.exp2q);
}

// log
export fn air2lean_libm_log_f16(x: u64) u64 {
    return narrow(f16, x, crt.log.__logh);
}
export fn air2lean_libm_log_f32(x: u64) u64 {
    return narrow(f32, x, crt.log.logf);
}
export fn air2lean_libm_log_f64(x: u64) u64 {
    return narrow(f64, x, crt.log.log);
}
export fn air2lean_libm_log_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.log.__logx);
}
export fn air2lean_libm_log_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.log.__logx);
}
export fn air2lean_libm_log_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.log.logq);
}
export fn air2lean_libm_log_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.log.logq);
}

// log2
export fn air2lean_libm_log2_f16(x: u64) u64 {
    return narrow(f16, x, crt.log2.__log2h);
}
export fn air2lean_libm_log2_f32(x: u64) u64 {
    return narrow(f32, x, crt.log2.log2f);
}
export fn air2lean_libm_log2_f64(x: u64) u64 {
    return narrow(f64, x, crt.log2.log2);
}
export fn air2lean_libm_log2_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.log2.__log2x);
}
export fn air2lean_libm_log2_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.log2.__log2x);
}
export fn air2lean_libm_log2_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.log2.log2q);
}
export fn air2lean_libm_log2_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.log2.log2q);
}

// log10
export fn air2lean_libm_log10_f16(x: u64) u64 {
    return narrow(f16, x, crt.log10.__log10h);
}
export fn air2lean_libm_log10_f32(x: u64) u64 {
    return narrow(f32, x, crt.log10.log10f);
}
export fn air2lean_libm_log10_f64(x: u64) u64 {
    return narrow(f64, x, crt.log10.log10);
}
export fn air2lean_libm_log10_f80_hi(hi: u64, lo: u64) u64 {
    return wideHi(f80, hi, lo, crt.log10.__log10x);
}
export fn air2lean_libm_log10_f80_lo(hi: u64, lo: u64) u64 {
    return wideLo(f80, hi, lo, crt.log10.__log10x);
}
export fn air2lean_libm_log10_f128_hi(hi: u64, lo: u64) u64 {
    return wideHi(f128, hi, lo, crt.log10.log10q);
}
export fn air2lean_libm_log10_f128_lo(hi: u64, lo: u64) u64 {
    return wideLo(f128, hi, lo, crt.log10.log10q);
}
