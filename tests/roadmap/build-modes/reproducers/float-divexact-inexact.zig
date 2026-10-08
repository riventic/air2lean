//! Reproducer: @divExact on floats with a non-integral quotient is illegal behaviour, but
//! ReleaseSafe does not check it, so the ReleaseSafe analyzed-AIR model (which does not throw) and
//! the ReleaseFast/ReleaseSmall builds disagree. Bits printed for 2^-1074 / 1.0 (the exact
//! quotient is 2^-1074, not an integer):
//!   zig run -OReleaseSafe tests/roadmap/build-modes/reproducers/float-divexact-inexact.zig  ->  0x0000000000000000
//!   zig run -OReleaseFast tests/roadmap/build-modes/reproducers/float-divexact-inexact.zig  ->  0x0000000000000001
const std = @import("std");

noinline fn divExact64(a: f64, b: f64) f64 {
    return @divExact(a, b);
}

pub fn main() void {
    const a: f64 = @bitCast(@as(u64, 1));
    const r: u64 = @bitCast(divExact64(a, 1.0));
    std.debug.print("0x{x:0>16}\n", .{r});
}
