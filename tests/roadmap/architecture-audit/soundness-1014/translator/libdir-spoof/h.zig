const std = @import("std");
/// With the modified std (create always fails) natively returns 0.
pub fn made(a: std.mem.Allocator) u32 {
    const p = a.create(u32) catch return 0;
    p.* = 5;
    const v = p.*;
    a.destroy(p);
    return v;
}
comptime { _ = &made; }
