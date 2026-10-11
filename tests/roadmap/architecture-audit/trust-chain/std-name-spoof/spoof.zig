const atomic = @import("atomic.zig");

/// Natively this always panics (the user's `atomic.spinLoopHint` panics).
export fn answer() u32 {
    atomic.spinLoopHint();
    return 42;
}
