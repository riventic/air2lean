//! Illegal behaviour inside `@setRuntimeSafety(false)` blocks of a ReleaseSafe build: the shapes
//! that the safety checks would otherwise cover (docs/illegal-behavior.md, former gaps). The model
//! must give `.illegal` or the translator must reject the function.

const S = struct { a: u32, b: u32 };
const Big = error{ A, B };
const Small = error{A};

/// A slice end past the length.
pub fn sliceEnd(s: *const []const u32, a: usize, b: usize) []const u32 {
    @setRuntimeSafety(false);
    return s.*[a..b];
}

/// A slice of an array pointer past its length.
pub fn sliceArray(p: *const [4]u32, a: usize, b: usize) []const u32 {
    @setRuntimeSafety(false);
    return p[a..b];
}

/// A start after the end.
pub fn sliceStart(s: *const []const u32, a: usize, b: usize) []const u32 {
    @setRuntimeSafety(false);
    return s.*[a..b];
}

/// Sentinel slicing of bytes: the 0.16.0 export records the sentinel value.
pub fn sentinelBytes(s: []const u8, n: usize) [:0]const u8 {
    @setRuntimeSafety(false);
    return s[0..n :0];
}

/// Sentinel slicing of `u16` items: no recorded sentinel value, so the translator rejects it.
pub fn sentinelWords(s: []const u16, n: usize) [:0]const u16 {
    @setRuntimeSafety(false);
    return s[0..n :0];
}

/// `for` over two slices of unequal length (pure function).
pub fn forLen(a: []const u32, b: []const u32) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a, b) |x, y| sum +%= x +% y;
    return sum;
}

/// `for` over two slices of unequal length (function that uses memory).
pub fn forLenMem(a: *const []const u32, b: *const []const u32) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a.*, b.*) |x, y| sum +%= x +% y;
    return sum;
}

/// `for` over a slice and a range of unequal length.
pub fn forRange(a: []const u32, n: usize) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a, 0..n) |x, i| sum +%= x +% @as(u32, @truncate(i));
    return sum;
}

/// `@fieldParentPtr` of a pointer that is not to that field.
pub fn parentOf(p: *u32) *S {
    @setRuntimeSafety(false);
    return @fieldParentPtr("b", p);
}

/// `@errorCast` of an error union, without and with safety.
pub fn errorCastUnion(e: Big!u32) Small!u32 {
    @setRuntimeSafety(false);
    return @errorCast(e);
}

pub fn errorCastUnionSafe(e: Big!u32) Small!u32 {
    return @errorCast(e);
}

comptime {
    _ = &sliceEnd;
    _ = &sliceArray;
    _ = &sliceStart;
    _ = &sentinelBytes;
    _ = &sentinelWords;
    _ = &forLen;
    _ = &forLenMem;
    _ = &forRange;
    _ = &parentOf;
    _ = &errorCastUnion;
    _ = &errorCastUnionSafe;
}
