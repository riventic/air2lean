//! `@divCeil` (Zig 0.17.0) on signed and unsigned integers: the compiler-exported fixture of the
//! `support:tags:div_ceil` qualification obligation (`check.sh`). Sema guards the `div_ceil`
//! instruction with the `@divFloor` safety checks: division by zero, and `minInt / -1` for a
//! signed type.
pub fn divCeilI8(a: i8, b: i8) i8 {
    return @divCeil(a, b);
}
pub fn divCeilU8(a: u8, b: u8) u8 {
    return @divCeil(a, b);
}
pub fn divCeilI32(a: i32, b: i32) i32 {
    return @divCeil(a, b);
}
pub fn divCeilU32(a: u32, b: u32) u32 {
    return @divCeil(a, b);
}
pub fn divCeilI64(a: i64, b: i64) i64 {
    return @divCeil(a, b);
}
pub fn divCeilU64(a: u64, b: u64) u64 {
    return @divCeil(a, b);
}
pub fn divCeilI13(a: i13, b: i13) i13 {
    return @divCeil(a, b);
}

comptime {
    _ = &divCeilI8;
    _ = &divCeilU8;
    _ = &divCeilI32;
    _ = &divCeilU32;
    _ = &divCeilI64;
    _ = &divCeilU64;
    _ = &divCeilI13;
}
