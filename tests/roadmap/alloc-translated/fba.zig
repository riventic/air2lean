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

// M02: growth through `remap` (`how` 0) and `realloc` (1), observed as one word, as `page.zig`'s
// `page_grow` (`native.zig` prints the same words from the native run):
//   bit 0  the call returned a block          bit 1  at another address (the block moved)
//   bit 2  the kept bytes are the old ones    bit 3  the block's last byte is writable
//   bit 4  the block behind it kept its bytes (`behind`)
//   bits 8 and up: the buffer's `end_index` afterwards (what the allocations use up)
// A failed call gives bit 2 (and 4) alone: the old block is still live, with its bytes and length.

fn pattern(i: usize) u8 {
    return @truncate(i *% 31 +% 7);
}

fn kept(s: []const u8) bool {
    for (s, 0..) |b, i| {
        if (b != pattern(i)) return false;
    }
    return true;
}

/// A block of `n` bytes (holding `pattern`) grows or shrinks to `m > 0` bytes. With `behind`, an
/// 8-byte block is allocated after it, so it is not the buffer's last allocation.
pub export fn fba_grow(n: usize, m: usize, how: u8, behind: bool) u64 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const a = fba.allocator();
    const s = a.alloc(u8, n) catch return 32;
    for (s, 0..) |*b, i| b.* = pattern(i);
    const t: []u8 = if (behind) a.alloc(u8, 8) catch return 32 else &.{};
    @memset(t, 0x5A);
    const got: ?[]u8 = if (how == 0) a.remap(s, m) else a.realloc(s, m) catch null;
    var r: u64 = 0;
    if (got) |g| {
        r |= 1;
        if (@intFromPtr(g.ptr) != @intFromPtr(s.ptr)) r |= 2;
        if (kept(g[0..@min(n, m)])) r |= 4;
        g[m - 1] = 0xA5;
        if (g[m - 1] == 0xA5) r |= 8;
    } else if (kept(s)) r |= 4;
    var same = behind;
    for (t) |b| {
        if (b != 0x5A) same = false;
    }
    if (same) r |= 16;
    return r | @as(u64, fba.end_index) << 8;
}

pub export fn fba_reset(n: usize) usize {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    const a = fba.allocator();
    _ = a.alloc(u8, n) catch return 0;
    fba.reset();
    const t = a.alloc(u8, n) catch return 1;
    return fba.end_index + t.len;
}
