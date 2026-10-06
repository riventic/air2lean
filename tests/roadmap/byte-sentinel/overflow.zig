const std = @import("std");
const common = @import("common");
const source = @import("source.zig");
var ta: common.TestAllocator = .{ .request_cap = 0 };
pub const panic = std.debug.FullPanic(overflowPanic);
fn overflowPanic(message: []const u8, _: ?usize) noreturn {
    if (!std.mem.eql(u8, message, "integer overflow") or ta.count != 0) std.process.exit(2);
    std.debug.print("overflow-before-allocation\n", .{});
    std.process.exit(0);
}
pub fn main() !void {
    _ = try source.makeByte(ta.allocator(), std.math.maxInt(usize));
    return error.AcceptedOverflow;
}
