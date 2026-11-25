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

// M02: growth through `remap` and `realloc`, observed as one word (`native.zig` prints the same
// words from the native run).
//   bit 0  the call returned a block          bit 1  at another address (the block moved)
//   bit 2  the kept bytes are the old ones    bit 3  the block's last byte is writable
//   bit 4  a neighbouring live block kept its bytes (`page_grow_blocked`)
// A failed call gives bit 2 alone: the old block is still live, with its bytes and length.

fn pattern(i: usize) u8 {
    return @truncate(i *% 31 +% 7);
}

fn kept(s: []const u8) bool {
    for (s, 0..) |b, i| {
        if (b != pattern(i)) return false;
    }
    return true;
}

/// `s` (holding `pattern`) grows or shrinks to `m` bytes, by `remap` or (`how != 0`) by
/// `realloc`; the block that is live afterwards is written and freed.
fn grow(a: std.mem.Allocator, s: []u8, m: usize, how: u8) u64 {
    const old = @intFromPtr(s.ptr);
    const len = s.len;
    var got: ?[]u8 = null;
    if (how == 0) {
        got = a.remap(s, m);
    } else {
        got = a.realloc(s, m) catch null;
    }
    if (got) |t| {
        var r: u64 = 1;
        if (@intFromPtr(t.ptr) != old) r |= 2;
        if (kept(t[0..@min(len, m)])) r |= 4;
        t[m - 1] = 0xA5;
        if (t[m - 1] == 0xA5) r |= 8;
        a.free(t);
        return r;
    }
    const r: u64 = if (kept(s)) 4 else 0;
    s[len - 1] = 0xA5;
    a.free(s);
    return r;
}

/// A block of `n` bytes is cut to `keep` bytes by `resize` (the pages after it are free address
/// space then) and grows to `m` bytes.
pub export fn page_grow(n: usize, keep: usize, m: usize, how: u8) u64 {
    const a = std.heap.page_allocator;
    var s = a.alloc(u8, n) catch return 32;
    if (keep < n) {
        if (!a.resize(s, keep)) {
            a.free(s);
            return 64;
        }
        s = s[0..keep];
    }
    for (s, 0..) |*b, i| b.* = pattern(i);
    return grow(a, s, m, how);
}

/// Two live blocks of `n` bytes; the lower one grows to one byte into the higher one's pages, so
/// it cannot grow in place.
pub export fn page_grow_blocked(n: usize, how: u8) u64 {
    const a = std.heap.page_allocator;
    const x = a.alloc(u8, n) catch return 32;
    const y = a.alloc(u8, n) catch {
        a.free(x);
        return 32;
    };
    var lo = x;
    var hi = y;
    if (@intFromPtr(y.ptr) < @intFromPtr(x.ptr)) {
        lo = y;
        hi = x;
    }
    for (lo, 0..) |*b, i| b.* = pattern(i);
    @memset(hi, 0x5A);
    var r = grow(a, lo, @intFromPtr(hi.ptr) - @intFromPtr(lo.ptr) + 1, how);
    var same = true;
    for (hi) |b| {
        if (b != 0x5A) same = false;
    }
    if (same) r |= 16;
    a.free(hi);
    return r;
}

/// `page_grow_blocked`, but after a growth that moved the block its old address is read: the old
/// block is gone. 0 when the growth failed or stayed in place.
pub export fn page_grow_stale(n: usize, how: u8) u64 {
    const a = std.heap.page_allocator;
    const x = a.alloc(u8, n) catch return 0;
    const y = a.alloc(u8, n) catch {
        a.free(x);
        return 0;
    };
    var lo = x;
    var hi = y;
    if (@intFromPtr(y.ptr) < @intFromPtr(x.ptr)) {
        lo = y;
        hi = x;
    }
    lo[0] = 7;
    const m = @intFromPtr(hi.ptr) - @intFromPtr(lo.ptr) + 1;
    var got: ?[]u8 = null;
    if (how == 0) {
        got = a.remap(lo, m);
    } else {
        got = a.realloc(lo, m) catch null;
    }
    var r: u64 = 0;
    if (got) |t| {
        if (@intFromPtr(t.ptr) != @intFromPtr(lo.ptr)) r = @as(u64, lo[0]) + 1;
        a.free(t);
    } else {
        a.free(lo);
    }
    a.free(hi);
    return r;
}
