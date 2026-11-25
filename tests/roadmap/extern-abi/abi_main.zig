//! The root of the AIR export of `abi.zig` (`zig translate-c` of `abi.c`) with Zig's libc in
//! the same compilation (`build-exe -lc`, as `tests/roadmap/c-frontend/run.py` exports a corpus
//! file), so that its extern calls bind to Zig libc's definitions (`export-table.air2lean`).
comptime {
    _ = @import("abi.zig");
}

pub fn main() void {}
