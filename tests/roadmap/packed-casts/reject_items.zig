//! L07, rejected: array items that Zig 0.14.1 and 0.15.2 accept in a `@bitCast` because Sema
//! checks only the outer types there (Zig 0.16.0 and 0.17.1: compile errors, `compile-errors/`),
//! and that the model does not reinterpret:
//!   * a tuple: the memory model has no tuple layout;
//!   * error storage (an error set or an error union): the model's error bytes are symbolic, not
//!     the compilation's error codes;
//!   * an optional of one of these or of a pointer (pointer bytes carry provenance). Other
//!     optionals are memory reinterpretations (`opt_items.zig`).
//! Each function is translated alone and must be rejected with its diagnostic (`check.sh`,
//! `reject/expected.txt`).
pub const Pair = struct { u8, u16 };
pub const E = error{ A, B };

pub fn tuplesToInt(a: [2]Pair) u64 {
    return @bitCast(a);
}

pub fn intToTuples(x: u64) u16 {
    const a: [2]Pair = @bitCast(x);
    return a[1][1];
}

pub fn errorsToInt(a: [2]E) u32 {
    return @bitCast(a);
}

pub fn intToErrors(x: u32) bool {
    const a: [2]E = @bitCast(x);
    return a[0] == error.A;
}

pub fn errorUnionsToInt(a: [2]E!u16) u64 {
    return @bitCast(a);
}

pub fn optTuplesToInt(a: [2]?Pair) u96 {
    return @bitCast(a);
}

pub fn optErrorsToInt(a: [2]?E) u32 {
    return @bitCast(a);
}

pub fn optPtrsToInt(a: [2]?*u8) u128 {
    return @bitCast(a);
}

pub fn intToOptPtrs(x: u128) bool {
    const a: [2]?*u8 = @bitCast(x);
    return a[1] == null;
}

comptime {
    _ = &tuplesToInt;
    _ = &intToTuples;
    _ = &errorsToInt;
    _ = &intToErrors;
    _ = &errorUnionsToInt;
    _ = &optTuplesToInt;
    _ = &optErrorsToInt;
    _ = &optPtrsToInt;
    _ = &intToOptPtrs;
}
