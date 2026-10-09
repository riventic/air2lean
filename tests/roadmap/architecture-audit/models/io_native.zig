//! Native side of the `std.Io` divergences: real `std.Io` implementations, stock Zig 0.16.0.
//! No argument: `cancelProbe` on a `std.Io.Threaded`. Any argument: `handoffProbe` on
//! `std.Io.Threaded.global_single_threaded` (expected to hang; run it under a timeout).
const std = @import("std");
const probe = @import("io_probe.zig");

pub fn main(init: std.process.Init.Minimal) !void {
    if (init.args.vector.len > 1) {
        const r = probe.handoffProbe(std.Io.Threaded.global_single_threaded.io());
        std.debug.print("handoffProbe(single_threaded)={d}\n", .{r});
        return;
    }
    var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
    defer threaded.deinit();
    const r = probe.cancelProbe(threaded.io());
    std.debug.print("cancelProbe(Threaded)={d}\n", .{r});
}
