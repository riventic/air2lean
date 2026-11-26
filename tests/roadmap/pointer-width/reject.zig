//! T02 rejections: wasm32 operations that the 32-bit pointer model does not parameterize.
const std = @import("std");

pub fn atomicRead(p: *const u32) u32 {
    return @atomicLoad(u32, p, .seq_cst);
}

pub fn copyOf(a: std.mem.Allocator, s: []const u8) ![]u8 {
    return a.dupe(u8, s);
}

comptime {
    _ = &atomicRead;
    _ = &copyOf;
}
