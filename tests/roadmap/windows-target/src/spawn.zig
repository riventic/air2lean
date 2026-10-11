//! A `std.Thread.spawn`: the std thread model needs the target's OS layer.
const std = @import("std");

fn work(x: *u32) void {
    x.* += 1;
}

export fn spawnOne() u32 {
    var x: u32 = 0;
    const t = std.Thread.spawn(.{}, work, .{&x}) catch return 0;
    t.join();
    return x;
}
