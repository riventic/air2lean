const std = @import("std");

var buffer: [4096]u8 = undefined;

pub export fn arena_sum(n: usize) u64 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return 0;
    @memset(s, 1);
    var sum: u64 = 0;
    for (s) |b| sum += b;
    a.free(s);
    return sum;
}

pub export fn arena_resize(n: usize, m: usize) bool {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return false;
    return a.resize(s, m);
}

pub export fn arena_reset(n: usize, retain: bool) usize {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    _ = a.alloc(u8, n) catch return 0;
    _ = a.alloc(u8, n) catch return 1;
    const ok = arena.reset(if (retain) .retain_capacity else .free_all);
    const t = a.alloc(u8, n) catch return 2;
    return @intFromBool(ok) + 2 * t.len + 4 * arena.queryCapacity();
}

pub export fn arena_page(n: usize) u64 {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const p = a.create(u64) catch return 0;
    p.* = n;
    const s = a.alloc(u8, n) catch return 1;
    @memset(s, 2);
    return p.* + s[0];
}
