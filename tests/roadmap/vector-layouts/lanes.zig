//! L09 lane pointers into bit-packed vectors: `&v[i]` of `@Vector(n, T)` whose lanes are not
//! power-of-two bytes (`u3`, `u9`, `u24`, `bool`) is a pointer to the whole vector with a lane
//! index (`*align(a:0:n:i) T`). The translator models it as a bit-pointer into the vector's
//! `n * @bitSizeOf(T)`-bit integer: host `ceil(n * W / 8)` bytes, bit offset `i * W`.
//! `zig test` checks the native results; `lanes_check.py` exports the AIR and checks the
//! translated functions against the same results.
const std = @import("std");

const V9 = @Vector(4, u9);
const V3 = @Vector(8, u3);
const V24 = @Vector(3, u24);
const B5 = @Vector(5, bool);

// Lane pointer types, as `&v[i]` makes them.
const Lane3 = @TypeOf(&@as(*V3, undefined)[5]);
const LaneB = @TypeOf(&@as(*B5, undefined)[3]);

comptime {
    // A lane pointer is a pointer to the lane type, not to the vector, and needs no offset.
    std.debug.assert(@typeInfo(Lane3).pointer.child == u3);
    std.debug.assert(@typeInfo(LaneB).pointer.child == bool);
    std.debug.assert(@sizeOf(V9) == 8 and @sizeOf(V3) == 4 and @sizeOf(V24) == 16 and @sizeOf(B5) == 1);
}

noinline fn putU3(p: Lane3, x: u3) void {
    p.* = x;
}

noinline fn getU3(p: Lane3) u3 {
    return p.*;
}

noinline fn flipBool(p: LaneB) void {
    p.* = !p.*;
}

/// Lane 2 of a `u9` vector: a store, then a load, through `&v[2]`.
export fn u9Lane(a: u16, b: u16, x: u16) u64 {
    var v: V9 = .{ @truncate(a), @truncate(b), @truncate(a), @truncate(b) };
    const p = &v[2];
    p.* = @truncate(x);
    const y: u64 = p.*;
    const w: [4]u9 = v;
    return @as(u64, w[0]) | @as(u64, w[1]) << 9 | @as(u64, w[2]) << 18 | @as(u64, w[3]) << 27 | y << 36;
}

/// Lane 5 of a `u3` vector, through a lane pointer parameter.
export fn u3Lane(seed: u32, x: u8) u32 {
    var v: V3 = undefined;
    inline for (0..8) |i| v[i] = @truncate(seed >> (3 * i));
    putU3(&v[5], @truncate(x));
    const y: u32 = getU3(&v[5]);
    const w: [8]u3 = v;
    var r: u32 = 0;
    inline for (0..8) |i| r |= @as(u32, w[i]) << (3 * i);
    return r | y << 24;
}

/// Lane 1 of a `u24` vector: the host is 9 bytes, wider than a register.
export fn u24Lane(a: u32, x: u32) u32 {
    var v: V24 = .{ @truncate(a), @truncate(a >> 8), @truncate(a +% 1) };
    const p = &v[1];
    p.* = @truncate(x);
    const w: [3]u24 = v;
    return (w[0] ^ w[2]) +% w[1];
}

/// Lane 3 of a `bool` vector, flipped through a lane pointer parameter.
export fn boolLane(bits: u8) u8 {
    var v: B5 = undefined;
    inline for (0..5) |i| v[i] = (bits >> i) & 1 != 0;
    flipBool(&v[3]);
    const w: [5]bool = v;
    var r: u8 = 0;
    inline for (0..5) |i| r |= @as(u8, @intFromBool(w[i])) << i;
    return r;
}

/// The expected results: the lanes are independent `uW` values.
fn u9Expect(a: u16, b: u16, x: u16) u64 {
    const a9: u64 = @as(u9, @truncate(a));
    const b9: u64 = @as(u9, @truncate(b));
    const x9: u64 = @as(u9, @truncate(x));
    return a9 | b9 << 9 | x9 << 18 | b9 << 27 | x9 << 36;
}

fn u3Expect(seed: u32, x: u8) u32 {
    const x3: u32 = @as(u3, @truncate(x));
    return (seed & 0xffffff & ~@as(u32, 7 << 15)) | x3 << 15 | x3 << 24;
}

fn u24Expect(a: u32, x: u32) u32 {
    const lo: u24 = @truncate(a);
    const hi: u24 = @truncate(a +% 1);
    return (lo ^ hi) +% @as(u24, @truncate(x));
}

test "lane pointers read and write exactly their lane" {
    for ([_][3]u16{ .{ 0, 0, 0 }, .{ 0x1ff, 0, 0xaa }, .{ 0x155, 0x0aa, 0x1ff }, .{ 0xffff, 0x1234, 7 } }) |c| {
        try std.testing.expectEqual(u9Expect(c[0], c[1], c[2]), u9Lane(c[0], c[1], c[2]));
    }
    for ([_]u32{ 0, 0xffffff, 0x123456, 0xfac688 }) |s| {
        for ([_]u8{ 0, 5, 7, 0xff }) |x| try std.testing.expectEqual(u3Expect(s, x), u3Lane(s, x));
    }
    for ([_]u32{ 0, 0xabcdef12, 0xffffffff }) |a| {
        for ([_]u32{ 0, 0x00fedcba, 0x12345678 }) |x| try std.testing.expectEqual(u24Expect(a, x), u24Lane(a, x));
    }
    for (0..32) |n| {
        const bits: u8 = @intCast(n);
        try std.testing.expectEqual(bits ^ 8, boolLane(bits));
    }
}
