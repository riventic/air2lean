//! One call site, a closure allocator and an environment one (docs/interfaces.md): `make`
//! takes its allocator as a parameter; `withFba` passes the program's own
//! `FixedBufferAllocator`. The dispatch in the `std.mem.Allocator` wrappers tests the
//! FixedBufferAllocator's functions first and calls the environment only for any other pointer.

const std = @import("std");

/// A new `u32` holding `v`, from any allocator.
pub fn make(a: std.mem.Allocator, v: u32) !*u32 {
    const p = try a.create(u32);
    p.* = v;
    return p;
}

/// `make` through the program's own fixed buffer.
pub fn withFba() !u32 {
    var buf: [64]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buf);
    const p = try make(fba.allocator(), 7);
    return p.*;
}

comptime {
    _ = &make;
    _ = &withFba;
}
