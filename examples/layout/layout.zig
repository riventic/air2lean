//! M20: casts (`@intFromPtr`, `@ptrFromInt`, `@ptrCast`, `@constCast`, `@volatileCast`,
//! `@alignCast`) and `@fieldParentPtr`. `packed`/`extern` layout, unions/error unions in memory,
//! and function pointers are outside this milestone's scope (PLAN.md).

pub const Point = struct {
    x: u32,
    y: u32,
};

/// Two pointers are equal iff their addresses are (`@intFromPtr`).
pub fn addrEq(a: *const u32, b: *const u32) bool {
    return @intFromPtr(a) == @intFromPtr(b);
}

/// A pointer through its own address and back (`@intFromPtr` then `@ptrFromInt`): the identity.
pub fn ptrRoundTrip(p: *u32) *u32 {
    return @ptrFromInt(@intFromPtr(p));
}

/// The pointer at address `a` (`@ptrFromInt`; panics `castToNull` if `a` is 0,
/// `incorrectAlignment` if `a` is not a multiple of 4). A non-panicking `@ptrFromInt` is already
/// exercised through `ptrRoundTrip`: a valid address here would need a real allocation, since the
/// diff-test harness reads back the pointee.
pub fn ptrFromAddr(a: usize) *u32 {
    return @ptrFromInt(a);
}

/// `p` viewed as `const` (`@ptrCast`).
pub fn asConst(p: *u32) *const u32 {
    return @ptrCast(p);
}

/// `p` with `const` removed (`@constCast`).
pub fn dropConst(p: *const u32) *u32 {
    return @constCast(p);
}

/// `p` viewed as `volatile` (`@volatileCast`).
pub fn asVolatile(p: *u32) *volatile u32 {
    return @volatileCast(p);
}

/// `p` re-aligned to 4 (`@alignCast`; panics `incorrectAlignment` if `p`'s address is not a
/// multiple of 4).
pub fn align4(p: *align(1) u32) *align(4) u32 {
    return @alignCast(p);
}

/// The `Point` that has `xp` as its `x` field (`@fieldParentPtr`).
pub fn parentOfX(xp: *u32) *Point {
    return @fieldParentPtr("x", xp);
}

/// The `Point` that has `yp` as its `y` field.
pub fn parentOfY(yp: *u32) *Point {
    return @fieldParentPtr("y", yp);
}

comptime {
    _ = &addrEq;
    _ = &ptrRoundTrip;
    _ = &ptrFromAddr;
    _ = &asConst;
    _ = &dropConst;
    _ = &asVolatile;
    _ = &align4;
    _ = &parentOfX;
    _ = &parentOfY;
}
