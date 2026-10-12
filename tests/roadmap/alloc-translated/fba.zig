const std = @import("std");

var buffer: [256]u8 = undefined;

pub export fn fba_sum(n: usize) u64 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const a = fba.allocator();
    const s = a.alloc(u8, n) catch return 0;
    @memset(s, 1);
    var sum: u64 = 0;
    for (s) |b| sum += b;
    a.free(s);
    return sum;
}

pub export fn fba_create(v: u32) u32 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const a = fba.allocator();
    const p = a.create(u32) catch return 0;
    p.* = v;
    const r = p.*;
    a.destroy(p);
    return r;
}

pub export fn fba_resize(n: usize, m: usize) bool {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const a = fba.allocator();
    const s = a.alloc(u8, n) catch return false;
    return a.resize(s, m);
}

pub export fn fba_reset(n: usize) usize {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const a = fba.allocator();
    _ = a.alloc(u8, n) catch return 0;
    fba.reset();
    const t = a.alloc(u8, n) catch return 1;
    return fba.end_index + t.len;
}
