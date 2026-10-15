// Audit 2026-10-14, S1: the native program behind `NonStrict.lean`'s `main`.
// `@bitCast` of a NaN to an integer is not illegal behaviour; only the bits are unspecified.
// The model throws `.unspecified`; native code returns the bits and the program goes on.
const std = @import("std");

pub fn main() void {
    var x: f64 = std.math.nan(f64);
    _ = &x;
    const bits: u64 = @bitCast(x);
    std.debug.print("{x}\n", .{bits});
}
