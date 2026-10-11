const Thread = @import("Thread.zig");

/// Reads the user struct's field. A `Thread` read by name as the std handle type has no fields.
export fn threadId(t: *const Thread) u32 {
    return t.id;
}
