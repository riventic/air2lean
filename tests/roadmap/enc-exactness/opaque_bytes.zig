//! The bytes of a model handle viewed as other data (docs/architecture-audit/enc-exactness.md):
//! the model stores `std.mem.Allocator` as 16 zero bytes, so this view would read 0 where native
//! code reads the allocator's `vtable` address. The translator rejects the pointer cast.
const std = @import("std");

/// The second word of a `std.mem.Allocator` (its `vtable`) read as an integer.
pub fn allocatorWord(a: std.mem.Allocator) u64 {
    var c = a;
    _ = &c;
    return @as(*const [2]u64, @ptrCast(&c))[1];
}

comptime {
    _ = &allocatorWord;
}
