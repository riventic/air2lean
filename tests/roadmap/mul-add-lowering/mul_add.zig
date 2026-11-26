//! `@mulAdd` per float format. Exported for x86_64-linux at three CPUs (exports.json): the
//! baseline (no multiply-add instruction: compiler_rt's routines, the model's rule), `haswell`
//! (`fma`: `vfmadd…` for f32 and f64) and `sapphirerapids` (also `avx512fp16`: `vfmadd…sh` for
//! f16). The checker admits a `@mulAdd` only where the profile's lowering is the model's
//! (`CheckCtx.checkMulAdd`); `test_cli.py` has the expected verdict of each function.
pub fn fma16(a: f16, b: f16, c: f16) f16 {
    return @mulAdd(f16, a, b, c);
}
pub fn fma32(a: f32, b: f32, c: f32) f32 {
    return @mulAdd(f32, a, b, c);
}
pub fn fma64(a: f64, b: f64, c: f64) f64 {
    return @mulAdd(f64, a, b, c);
}
pub fn fma80(a: f80, b: f80, c: f80) f80 {
    return @mulAdd(f80, a, b, c);
}
pub fn fma128(a: f128, b: f128, c: f128) f128 {
    return @mulAdd(f128, a, b, c);
}
pub fn fmaVec(a: @Vector(4, f32), b: @Vector(4, f32), c: @Vector(4, f32)) @Vector(4, f32) {
    return @mulAdd(@Vector(4, f32), a, b, c);
}
comptime {
    _ = &fma16;
    _ = &fma32;
    _ = &fma64;
    _ = &fma80;
    _ = &fma128;
    _ = &fmaVec;
}
