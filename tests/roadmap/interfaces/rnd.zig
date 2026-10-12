//! The second interface (docs/interfaces.md): `std.Random`, whose `fillFn` the caller supplies.

const std = @import("std");

/// A die roll from one byte of `r`: 1 to 6.
pub fn roll(r: std.Random) u8 {
    var b: [1]u8 = undefined;
    r.bytes(&b);
    return b[0] % 6 + 1;
}

comptime {
    _ = &roll;
}
