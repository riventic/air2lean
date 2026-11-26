//! `@alignCast` with runtime safety off, for every shape of pointer cast
//! (docs/illegal-behavior.md row 20), exported by every supported Zig version
//! (`align-air/<version>/`). Sema writes no alignment test here, so the cast itself must check
//! its operand's address in the model (`Zig.checkAlign`): a misaligned operand is illegal
//! behaviour, whatever else the cast does (unwrap, wrap, null conversion). Null passes.

/// `*T` → `*U`.
pub fn ptrToPtr(o: *u8) *u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `?*T` → `*U`: unwraps too.
pub fn optToPtr(o: ?*u8) *u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `?*T` → `?*U`.
pub fn optToOpt(o: ?*u8) ?*u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `?*T` → `?*align(8) T`: `@alignCast` alone.
pub fn optAlign(o: ?*u8) ?*align(8) u8 {
    @setRuntimeSafety(false);
    return @alignCast(o);
}

/// `*T` → `?*U`: wraps too.
pub fn ptrToOpt(o: *u8) ?*u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `?[*]T` → `[*]U`.
pub fn manyOptToMany(o: ?[*]u8) [*]u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `[*c]T` → `*U`: requires a nonzero address too.
pub fn cToPtr(o: [*c]u8) *u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `[*c]T` → `[*c]U`.
pub fn cToC(o: [*c]u8) [*c]u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `?*T` → `[*c]U`: null becomes address zero.
pub fn optToC(o: ?*u8) [*c]u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `[*c]T` → `?*U`: address zero becomes null.
pub fn cToOpt(o: [*c]u8) ?*u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `*allowzero T` → `*U`.
pub fn zeroToPtr(o: *allowzero u8) *u64 {
    @setRuntimeSafety(false);
    return @ptrCast(@alignCast(o));
}

/// `[]T` → `[]align(8) T`: the item pointer.
pub fn sliceAlign(o: []u8) []align(8) u8 {
    @setRuntimeSafety(false);
    return @alignCast(o);
}

/// No stricter alignment: no check.
pub fn optSame(o: ?*u64) *u32 {
    @setRuntimeSafety(false);
    return @ptrCast(o);
}

comptime {
    _ = &ptrToPtr;
    _ = &optToPtr;
    _ = &optToOpt;
    _ = &optAlign;
    _ = &ptrToOpt;
    _ = &manyOptToMany;
    _ = &cToPtr;
    _ = &cToC;
    _ = &optToC;
    _ = &cToOpt;
    _ = &zeroToPtr;
    _ = &sliceAlign;
    _ = &optSame;
}
