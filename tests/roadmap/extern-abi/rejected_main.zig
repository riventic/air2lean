//! The root of the AIR export of `rejected.zig` (`zig translate-c` of `rejected.c`) with Zig's
//! libc in the same compilation, as `abi_main.zig`.
comptime {
    _ = @import("rejected.zig");
}

pub fn main() void {}
