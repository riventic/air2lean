//! G5 (docs/c-frontend.md): container-level `var`s whose initial value is a comptime call
//! (`std.mem.zeroes`, as `zig translate-c` writes `static T x[N];`) and whose address escapes
//! (`&pool[i]`, `@intFromPtr(&data[1])`). Zig 0.16.0 Sema resolves only such a global's type
//! when a function takes its address and queues the value for later, so without the exporter's
//! eager resolution the AIR global had no `init`. Every export takes `(a, b)` and returns `u32`;
//! `native.zig` runs them natively.
const std = @import("std");

const Node = extern struct { value: u32, next: ?*Node };

var pool: [4]Node = std.mem.zeroes([4]Node);
var data: [4]u32 = std.mem.zeroes([4]u32);
var counter: u32 = blk: {
    var x: u32 = 0;
    for (0..5) |i| x += @intCast(i);
    break :blk x;
};

/// A list threaded through the global pool, summed with weights.
pub export fn poolList(a: u32, b: u32) u32 {
    var head: ?*Node = null;
    var i: u32 = 0;
    while (i < 4) : (i += 1) {
        pool[i] = .{ .value = a +% i *% b, .next = head };
        head = &pool[i];
    }
    var s: u32 = 0;
    var k: u32 = 1;
    var it = head;
    while (it) |n| : (it = n.next) {
        s +%= n.value *% k;
        k += 1;
    }
    return s;
}

/// An address round trip through an integer into the global array.
pub export fn dataAddr(a: u32, b: u32) u32 {
    for (&data, 0..) |*d, i| d.* = a +% @as(u32, @intCast(i)) *% b;
    const addr = @intFromPtr(&data[1]);
    const back: *u32 = @ptrFromInt(addr + @sizeOf(u32));
    return back.* +% @intFromBool(addr % @alignOf(u32) == 0);
}

/// A global initialised by a comptime block, read and written through a pointer.
pub export fn counterBump(a: u32, b: u32) u32 {
    const p = &counter;
    const before = p.*;
    p.* = before +% (a ^ b);
    const after = p.*;
    p.* = before;
    return after;
}
