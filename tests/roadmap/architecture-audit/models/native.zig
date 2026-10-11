//! Native side of the allocator divergences: the real std allocators, stock Zig 0.16.0.
const std = @import("std");
const probe = @import("alloc_probe.zig");

pub fn main() !void {
    var fba = std.heap.FixedBufferAllocator.init(&probe.arena_bytes);
    const alias = try probe.aliasProbe(fba.allocator());
    const remap = try probe.remapProbe(std.heap.page_allocator);
    std.debug.print("aliasProbe(FixedBufferAllocator)={d}\nremapProbe(page_allocator)={d}\n", .{ alias, remap });
}
