//! Pure checked address arithmetic shared by the exporter and independent kernel tests.
//! No block identity is created here. A traversal must separately prove its base is global.
const std = @import("std");
pub const Failure = error{Overflow, Depth};
pub const Walk = struct {
    off: u64,
    remaining: u32 = 64,

    pub fn add(off: u64, delta: u64) Failure!u64 {
        const sum = @addWithOverflow(off, delta);
        if (sum[1] != 0) return error.Overflow;
        return sum[0];
    }

    pub fn project(self: *Walk, delta: u64, parent_off: u64) Failure!void {
        if (self.remaining == 0) return error.Depth;
        // Compute before committing, so a failed projection preserves the prior state.
        const next = try add(try add(self.off, delta), parent_off);
        self.off = next;
        self.remaining -= 1;
    }
};

test "accumulates leaf, exact payload, and every parent offset" {
    var walk: Walk = .{ .off = 3 };
    try walk.project(2, 11);
    try walk.project(0, 17);
    try std.testing.expectEqual(@as(u64, 33), walk.off);
    try std.testing.expectEqual(@as(u32, 62), walk.remaining);
}

test "both overflow additions fail without committing partial state" {
    const max = std.math.maxInt(u64);
    try std.testing.expectEqual(max, try Walk.add(max, 0));
    try std.testing.expectEqual(max, try Walk.add(max - 1, 1));
    try std.testing.expectError(error.Overflow, Walk.add(max, 1));
    var delta: Walk = .{ .off = max };
    try std.testing.expectError(error.Overflow, delta.project(1, 0));
    try std.testing.expectEqual(max, delta.off);
    try std.testing.expectEqual(@as(u32, 64), delta.remaining);
    var parent: Walk = .{ .off = max - 1 };
    try std.testing.expectError(error.Overflow, parent.project(1, 1));
    try std.testing.expectEqual(max - 1, parent.off);
    try std.testing.expectEqual(@as(u32, 64), parent.remaining);
}

test "bounded recursion rejects a cycle or deep chain at the same boundary" {
    var walk: Walk = .{ .off = 0 };
    for (0..64) |_| try walk.project(0, 0);
    try std.testing.expectError(error.Depth, walk.project(0, 0));
    try std.testing.expectEqual(@as(u64, 0), walk.off);
    try std.testing.expectEqual(@as(u32, 0), walk.remaining);
}
