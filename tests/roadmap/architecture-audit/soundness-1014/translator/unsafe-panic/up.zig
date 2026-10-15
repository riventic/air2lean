const E = enum(u2) { a, b, c };
pub const U = union(enum) { a: u32, b: u32 };
pub const B = union { a: u32, b: u32 };

/// `@enumFromInt` of an unnamed value with runtime safety off: illegal behaviour; native
/// ReleaseSafe returns the bits (3 for x = 3).
pub fn enumUnsafe(x: u2) u2 {
    @setRuntimeSafety(false);
    const e: E = @enumFromInt(x);
    return @intFromEnum(e);
}

/// Inactive tagged-union field with runtime safety off: native returns the payload bits.
pub fn unionUnsafe(u: U) u32 {
    @setRuntimeSafety(false);
    return u.a;
}

/// Inactive bare-union field with runtime safety off.
pub fn bareUnsafe(b: B) u32 {
    @setRuntimeSafety(false);
    return b.a;
}

/// Bare union built locally, read the other field.
pub fn bareLocal(x: u32) u32 {
    @setRuntimeSafety(false);
    const b: B = .{ .b = x };
    return b.a;
}

/// Tagged union built locally, read the other field.
pub fn unionLocal(x: u32) u32 {
    @setRuntimeSafety(false);
    const u: U = .{ .b = x };
    return u.a;
}

/// `?*u32` to `*u32` with runtime safety off: native returns 0 for null.
pub fn optPtrUnsafe(p: ?*u32) usize {
    @setRuntimeSafety(false);
    const q: *u32 = @ptrCast(p);
    return @intFromPtr(q);
}

/// `[*c]u32` to `*u32` with runtime safety off.
pub fn cPtrUnsafe(p: [*c]u32) usize {
    @setRuntimeSafety(false);
    const q: *u32 = p;
    return @intFromPtr(q);
}

comptime {
    _ = &enumUnsafe;
    _ = &unionUnsafe;
    _ = &bareUnsafe;
    _ = &bareLocal;
    _ = &unionLocal;
    _ = &optPtrUnsafe;
    _ = &cPtrUnsafe;
}

/// Unsigned division by zero with runtime safety off.
pub fn divUnsafe(a: u32, b: u32) u32 {
    @setRuntimeSafety(false);
    return a / b;
}

/// Overflowing `+` with runtime safety off.
pub fn addUnsafe(a: u32, b: u32) u32 {
    @setRuntimeSafety(false);
    return a + b;
}

/// `@intCast` that truncates, runtime safety off.
pub fn intCastUnsafe(a: u32) u8 {
    @setRuntimeSafety(false);
    return @intCast(a);
}

comptime {
    _ = &divUnsafe;
    _ = &addUnsafe;
    _ = &intCastUnsafe;
}
