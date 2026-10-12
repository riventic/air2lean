const std = @import("std");

/// The fixed buffer allocator gets the first 12 bytes; the client keeps the last 4.
var buffer: [16]u8 = undefined;

/// The proved client (`AllocFba/Client.lean`): alloc, write, realloc (the last allocation grows
/// in place), an allocation that does not fit (out of memory), free of the last allocation,
/// reset and a fresh allocation of the whole buffer.
pub export fn fba_client(v: u8) u32 {
    var fba = std.heap.FixedBufferAllocator.init(buffer[0..12]);
    const a = fba.allocator();
    const s = a.alloc(u8, 4) catch return 1;
    @memset(s, v);
    const t = a.realloc(s, 8) catch return 2;
    t[7] = v +% 1;
    if (a.alloc(u8, 64)) |big| {
        a.free(big);
        return 3;
    } else |_| {}
    const r = @as(u32, t[0]) + t[3] + t[7];
    a.free(t);
    fba.reset();
    const u = a.alloc(u8, 12) catch return 4;
    u[11] = v;
    buffer[15] = u[11];
    a.free(u);
    return r;
}

/// The remaining `std.mem.Allocator` wrappers, for the wrapper bridge (`AllocFba/Bridge.lean`).
pub export fn fba_create(v: u32) u32 {
    var fba = std.heap.FixedBufferAllocator.init(buffer[0..12]);
    const a = fba.allocator();
    const p = a.create(u32) catch return 0;
    p.* = v;
    const r = p.*;
    a.destroy(p);
    return r;
}

pub export fn fba_aligned(n: usize) usize {
    var fba = std.heap.FixedBufferAllocator.init(buffer[0..12]);
    const a = fba.allocator();
    _ = a.alloc(u8, 1) catch return 0;
    const s = a.alignedAlloc(u8, .@"4", n) catch return 1;
    const r = @intFromPtr(s.ptr) % 4;
    a.free(s);
    return r + s.len;
}

pub export fn fba_dupe(v: u8) u8 {
    var fba = std.heap.FixedBufferAllocator.init(buffer[0..12]);
    const a = fba.allocator();
    const src = [_]u8{ v, v +% 1, v +% 2 };
    const d = a.dupe(u8, &src) catch return 0;
    const r = d[2];
    a.free(d);
    return r;
}

pub export fn fba_sentinel(n: usize) u8 {
    var fba = std.heap.FixedBufferAllocator.init(buffer[0..12]);
    const a = fba.allocator();
    const s = a.allocSentinel(u8, n, 7) catch return 0;
    const r = s[n];
    a.free(s);
    return r;
}

pub export fn fba_realloc_move(v: u8) u8 {
    var fba = std.heap.FixedBufferAllocator.init(buffer[0..12]);
    const a = fba.allocator();
    const s = a.alloc(u8, 2) catch return 0;
    s[0] = v;
    _ = a.alloc(u8, 1) catch return 1;
    // `s` is not the last allocation: the realloc moves it.
    const t = a.realloc(s, 4) catch return 2;
    return t[0];
}
