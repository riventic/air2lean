const std = @import("std");
const posix = @import("posix.zig");

/// Natively always returns 0 (the user `posix.mmap` always fails).
pub fn mapped() u32 {
    const m = posix.mmap(null, 4096, .{ .READ = true, .WRITE = true }, .{ .TYPE = .PRIVATE, .ANONYMOUS = true }, -1, 0) catch return 0;
    m[0] = 7;
    return m[0];
}

comptime {
    _ = &mapped;
}
