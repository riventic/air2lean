/// `@shrExact` with runtime safety off: a shifted-out bit is illegal behaviour; native
/// ReleaseSafe returns the shifted value (shrUnsafe(3, 1) = 1).
pub fn shrUnsafe(a: u32, b: u5) u32 {
    @setRuntimeSafety(false);
    return @shrExact(a, b);
}

/// With safety: Sema checks the result after the op, the `shrOverflow` panic.
pub fn shrSafe(a: u32, b: u5) u32 {
    return @shrExact(a, b);
}

comptime {
    _ = &shrUnsafe;
    _ = &shrSafe;
}
