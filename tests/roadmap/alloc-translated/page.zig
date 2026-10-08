const std = @import("std");

pub export fn page_sum(n: usize) u64 {
    const a = std.heap.page_allocator;
    const s = a.alloc(u8, n) catch return 0;
    defer a.free(s);
    @memset(s, 1);
    var sum: u64 = 0;
    for (s) |b| sum += b;
    return sum;
}

pub export fn page_create(v: u32) u32 {
    const a = std.heap.page_allocator;
    const p = a.create(u32) catch return 0;
    p.* = v;
    const r = p.*;
    a.destroy(p);
    return r;
}

pub export fn page_resize(n: usize, m: usize) bool {
    const a = std.heap.page_allocator;
    const s = a.alloc(u8, n) catch return false;
    const ok = a.resize(s, m);
    if (ok) a.free(s.ptr[0..m]) else a.free(s);
    return ok;
}
