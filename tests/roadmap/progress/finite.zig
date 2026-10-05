//! Native smoke coverage only. No idle loop is executed and no termination claim is inferred.
const std = @import("std");
const progress = @import("progress.zig");

test "finite native progress calls accepting yield errors" {
    var failures: usize = 0;
    var caught_failures: usize = 0;
    for (0..64) |_| {
        progress.spinOnce();
        progress.yieldOnce() catch {
            failures += 1;
        };
        if (!progress.catchesYield()) caught_failures += 1;
    }
    std.debug.print("finite yield observations: {d} propagated errors, {d} caught errors\n", .{
        failures, caught_failures,
    });
}
