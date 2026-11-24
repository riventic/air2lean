//! L07: zero-bit types in a `@bitCast`. An array of `void` and `u0` have no bits and cast to each
//! other in every version. Sema folds every cast of a zero-bit type (its value is comptime-known),
//! so the compiler emits no `bitcast` for these functions; `air-handwritten/void_cast` has the
//! instruction itself.

pub fn voidsToInt(a: [4]void) u8 {
    const z: u0 = @bitCast(a);
    return z;
}

pub fn intToVoids(x: u0) usize {
    const v: [4]void = @bitCast(x);
    return v.len;
}

pub fn emptyToInt(a: [0]u8) u8 {
    const z: u0 = @bitCast(a);
    return z;
}

comptime {
    _ = &voidsToInt;
    _ = &intToVoids;
    _ = &emptyToInt;
}
