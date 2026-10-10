const std = @import("std");
const client = @import("client.zig");

pub fn main() void {
    std.debug.print("client {d} {d} {d}\n", .{ client.fba_client(0), client.fba_client(5), client.fba_client(255) });
    std.debug.print("create {d} aligned {d} {d} dupe {d} sentinel {d} {d} move {d}\n", .{
        client.fba_create(7),
        client.fba_aligned(3),
        client.fba_aligned(64),
        client.fba_dupe(9),
        client.fba_sentinel(4),
        client.fba_sentinel(20),
        client.fba_realloc_move(42),
    });
}
