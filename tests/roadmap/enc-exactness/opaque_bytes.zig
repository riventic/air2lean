//! The bytes of a model handle viewed as other data (docs/architecture-audit/model-handle-bytes.md):
//! native code reads the allocator's `vtable` address; the model has no such bytes
//! (`Byte.handle`), so it reads no value (`.unspecified`). It once read 0 (BUG-2).
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
