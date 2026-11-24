//! L07: Zig 0.17 accepts `void` itself in a `@bitCast` (`Type.hasBitRepresentation`; a compile
//! error before 0.17). It has no bits. Sema folds these casts (`void_casts.zig`).

pub fn voidToInt(v: void) u8 {
    const z: u0 = @bitCast(v);
    return z;
}

pub fn intToVoid(x: u0) void {
    return @bitCast(x);
}

pub fn emptyToVoid(a: [0]u8) void {
    return @bitCast(a);
}

pub fn voidToVoids(v: void) usize {
    const a: [3]void = @bitCast(v);
    return a.len;
}

comptime {
    _ = &voidToInt;
    _ = &intToVoid;
    _ = &emptyToVoid;
    _ = &voidToVoids;
}
