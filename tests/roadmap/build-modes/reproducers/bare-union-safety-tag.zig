//! Reproducer: a bare `union` has a hidden safety tag only when runtime safety is on, so its
//! layout differs between ReleaseSafe/Debug and ReleaseFast/ReleaseSmall
//! (docs/architecture-audit/2026-11-25-build-modes-0171.md). The ReleaseSafe analyzed-AIR model
//! has the ReleaseSafe layout; every line below is a legal execution on which an unchecked build
//! differs from it:
//!   zig run -OReleaseSafe tests/roadmap/build-modes/reproducers/bare-union-safety-tag.zig
//!     ->  size 8  len 8  buf a0b02a43012a5f8a
//!   zig run -OReleaseFast tests/roadmap/build-modes/reproducers/bare-union-safety-tag.zig
//!     ->  size 4  len 4  buf a0b02a43002a5f8a
//! (stock Zig 0.16.0 and 0.17.1 on aarch64-macos; ReleaseSmall as ReleaseFast, Debug as
//! ReleaseSafe; the 0.17.1 differential runs show the `setNum` bytes on all three targets). `numSize` returns a constant that Sema folded from the
//! ReleaseSafe layout; `numBytes` forms a slice whose length is that size, so an index in 4..7 is
//! in bounds for the model and illegal behaviour (no check) in the unchecked build; `setNum` is
//! `examples/layout`'s and writes the tag byte at offset 4, outside the 4-byte object of the
//! unchecked build.
const std = @import("std");

const Num = union {
    int: u32,
    small: u8,
};

noinline fn numSize() usize {
    return @sizeOf(Num);
}

noinline fn numBytes(buf: *const [8]u8) []const u8 {
    return buf[0..@sizeOf(Num)];
}

noinline fn setNum(p: *Num, big: bool, v: u32) void {
    p.* = if (big) .{ .int = v } else .{ .small = @truncate(v) };
}

pub fn main() void {
    var buf: [8]u8 align(8) = .{ 125, 176, 42, 67, 0, 42, 95, 138 };
    setNum(@ptrCast(&buf), false, 1443871136);
    std.debug.print("size {d}  len {d}  buf {x}\n", .{ numSize(), numBytes(&buf).len, buf });
}
