//! Illegal-behaviour fixtures (docs/illegal-behavior.md). Each function reaches one illegal
//! behaviour that no ReleaseSafe safety check catches, either because Sema never checks it
//! (`divExactSafe`, `toIntSafe`) or because the function disables runtime safety. The model must
//! give `.illegal` on those inputs. `check.sh` exports the analyzed AIR (ReleaseSafe), translates
//! it and evaluates the generated Lean (`Cases.lean`); `native.zig` prints what ReleaseSafe and
//! ReleaseFast builds return for the same inputs.

/// Float `@divExact` with safety: Sema checks only `floor(q) == q` of the truncated quotient.
pub fn divExactSafe(a: f64, b: f64) f64 {
    return @divExact(a, b);
}

/// Float `@divExact` without safety: AIR `div_exact`.
pub fn divExactUnsafe(a: f64, b: f64) f64 {
    @setRuntimeSafety(false);
    return @divExact(a, b);
}

/// Lane-wise float `@divExact` with safety (`reduce(And)` of the lane checks).
pub fn divExactLanes(a: @Vector(2, f64), b: @Vector(2, f64)) @Vector(2, f64) {
    return @divExact(a, b);
}

/// Integer `@divExact` without safety: AIR `div_exact`.
pub fn divExactIntUnsafe(a: i32, b: i32) i32 {
    @setRuntimeSafety(false);
    return @divExact(a, b);
}

/// `@shlExact` without safety: AIR `shl_exact`.
pub fn shlExactUnsafe(a: u32, b: u5) u32 {
    @setRuntimeSafety(false);
    return @shlExact(a, b);
}

/// A `u5` count can reach the width of a `u24` (24..31).
pub fn shl24Unsafe(a: u24, b: u5) u24 {
    @setRuntimeSafety(false);
    return a << b;
}

pub fn shr24Unsafe(a: u24, b: u5) u24 {
    @setRuntimeSafety(false);
    return a >> b;
}

/// `@intFromFloat` with safety: the range check is false for a NaN.
pub fn toIntSafe(x: f64) i32 {
    return @intFromFloat(x);
}

/// `@intFromFloat` without safety: AIR `int_from_float`.
pub fn toIntUnsafe(x: f64) i32 {
    @setRuntimeSafety(false);
    return @intFromFloat(x);
}

/// Overlapping `@memcpy` without safety (`docs/architecture-audit/trust-chain.md` finding 3).
pub fn copyOverlapUnsafe(buf: [*]u8, n: usize) void {
    @setRuntimeSafety(false);
    @memcpy(buf[1 .. n + 1], buf[0..n]);
}

/// `@memcpy` of two slices without safety: unequal lengths.
pub fn copyLenUnsafe(dst: []u8, src: []const u8) void {
    @setRuntimeSafety(false);
    @memcpy(dst, src);
}

/// A slice item read without safety, in a function that uses memory.
pub fn itemUnsafe(s: *const []const u32, i: usize) u32 {
    @setRuntimeSafety(false);
    return s.*[i];
}

comptime {
    _ = &divExactSafe;
    _ = &divExactUnsafe;
    _ = &divExactLanes;
    _ = &divExactIntUnsafe;
    _ = &shlExactUnsafe;
    _ = &shl24Unsafe;
    _ = &shr24Unsafe;
    _ = &toIntSafe;
    _ = &toIntUnsafe;
    _ = &copyOverlapUnsafe;
    _ = &copyLenUnsafe;
    _ = &itemUnsafe;
}
