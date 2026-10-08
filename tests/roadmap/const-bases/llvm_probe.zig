//! Native probe of the LLVM backend's constant `eu_payload` offset (README §LLVM).
//! `zig run llvm_probe.zig -fllvm` prints the constant and runtime payload offsets and the byte
//! read through each pointer. Zig semantics (and stage2_x86_64) give equal offsets and 22.
const std = @import("std");
const Failure = error{Bad};
const Holder = struct { head: u64, res: Failure![3]u8 };
const frozen: Holder = .{ .head = 1, .res = .{ 20, 21, 22 } };
var mutable: Holder = frozen;

noinline fn launder(p: *const u8) *const u8 {
    const q: *const volatile *const u8 = &p;
    return q.*;
}

pub fn main() void {
    const constant = launder(&(frozen.res catch unreachable)[2]);
    const runtime = launder(&(mutable.res catch unreachable)[2]);
    std.debug.print("constant={d} runtime={d} constant_read={d} runtime_read={d}\n", .{
        @intFromPtr(constant) - @intFromPtr(&frozen),
        @intFromPtr(runtime) - @intFromPtr(&mutable),
        constant.*,
        runtime.*,
    });
}
