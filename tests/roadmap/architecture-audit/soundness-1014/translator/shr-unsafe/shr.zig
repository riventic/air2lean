/// `@shrExact` with runtime safety off: a shifted-out bit is illegal behaviour; native
/// ReleaseSafe returns a poison-derived value (`illegal-behavior/native/`).
pub fn shrUnsafe(a: u32, b: u5) u32 {
    @setRuntimeSafety(false);
    return @shrExact(a, b);
}

/// With safety: Sema checks the result after the op (`shrOverflow`); ReleaseSafe deletes it.
pub fn shrSafe(a: u32, b: u5) u32 {
    return @shrExact(a, b);
}

comptime {
    _ = &shrUnsafe;
    _ = &shrSafe;
}
