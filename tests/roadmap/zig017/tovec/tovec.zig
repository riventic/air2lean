//! Zig 0.17.1's array-to-vector coercion (`array_to_vector`), the compiler-exported fixture of
//! its translation (`check.sh`): one function per vector lane kind the model has (integers of
//! whole-byte and other widths, `bool`, every float format) and arrays with a sentinel, which is
//! not a lane. Sema emits `array_to_vector` for a runtime array whose item type is the lane type.
pub fn toVecU8(a: [16]u8) @Vector(16, u8) {
    return a;
}
pub fn toVecI16(a: [3]i16) @Vector(3, i16) {
    return a;
}
pub fn toVecU24(a: [3]u24) @Vector(3, u24) {
    return a;
}
pub fn toVecI32(a: [4]i32) @Vector(4, i32) {
    return a;
}
pub fn toVecU64(a: [2]u64) @Vector(2, u64) {
    return a;
}
pub fn toVecI128(a: [2]i128) @Vector(2, i128) {
    return a;
}
pub fn toVecU1(a: [8]u1) @Vector(8, u1) {
    return a;
}
pub fn toVecI7(a: [5]i7) @Vector(5, i7) {
    return a;
}
pub fn toVecBool(a: [5]bool) @Vector(5, bool) {
    return a;
}
pub fn toVecF16(a: [3]f16) @Vector(3, f16) {
    return a;
}
pub fn toVecF32(a: [4]f32) @Vector(4, f32) {
    return a;
}
pub fn toVecF64(a: [2]f64) @Vector(2, f64) {
    return a;
}
pub fn toVecF80(a: [2]f80) @Vector(2, f80) {
    return a;
}
pub fn toVecF128(a: [2]f128) @Vector(2, f128) {
    return a;
}
pub fn toVecZ8(a: [5:0]u8) @Vector(5, u8) {
    return a;
}
pub fn toVecZ16(a: [3:7]i16) @Vector(3, i16) {
    return a;
}

comptime {
    _ = &toVecU8;
    _ = &toVecI16;
    _ = &toVecU24;
    _ = &toVecI32;
    _ = &toVecU64;
    _ = &toVecI128;
    _ = &toVecU1;
    _ = &toVecI7;
    _ = &toVecBool;
    _ = &toVecF16;
    _ = &toVecF32;
    _ = &toVecF64;
    _ = &toVecF80;
    _ = &toVecF128;
    _ = &toVecZ8;
    _ = &toVecZ16;
}
