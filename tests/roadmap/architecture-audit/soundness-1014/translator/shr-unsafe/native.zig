//! Native results of `shr.zig` on an inexact shift. Stock ReleaseSafe on aarch64-macos panics in
//! neither function and prints a value for both, `3` with 0.16.0 and `1` with 0.17.0: the op is
//! LLVM `lshr exact`, poison when a set bit is shifted out, and LLVM deletes Sema's `shrOverflow`
//! check after it. A Debug build panics in `shrSafe`.
//!   zig build-exe -OReleaseSafe --dep shr -Mroot=native.zig -Mshr=shr.zig && ./root
const std = @import("std");
const shr = @import("shr");
pub fn main() void {
    var a: u32 = 3;
    var b: u5 = 1;
    _ = &a;
    _ = &b;
    std.debug.print("shrUnsafe(3, 1) = {d}\n", .{shr.shrUnsafe(a, b)});
    std.debug.print("shrSafe(3, 1) = {d}\n", .{shr.shrSafe(a, b)});
}
