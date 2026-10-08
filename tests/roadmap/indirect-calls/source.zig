//! Source-native qualification of L11's callable-address table; no test-only AIR edits.
const std = @import("std");

const Unary = *const fn (u32) u32;

fn double(x: u32) u32 {
    return x *% 2;
}

fn succ(x: u32) u32 {
    return x +% 1;
}

fn square(x: u32) u32 {
    return x *% x;
}

/// A constant table: every declared target is reachable.
const table = [_]Unary{ &double, &succ, &square };

export fn viaTable(i: u32, x: u32) u32 {
    return table[i % 3](x);
}

/// A mutable global whose initializer is a function address.
var slot: Unary = &succ;

export fn viaGlobal(set: bool, x: u32) u32 {
    if (set) slot = &square;
    const f = slot;
    slot = &succ;
    return f(x);
}

const Ops = struct { f: Unary, k: u32 };

noinline fn viaField(ops: *const Ops, x: u32) u32 {
    return ops.f(x) +% ops.k;
}

export fn fieldCaller(x: u32) u32 {
    const ops = Ops{ .f = &square, .k = 4 };
    return viaField(&ops, x);
}

noinline fn twice(f: Unary, x: u32) u32 {
    return f(f(x));
}

export fn viaParam(sq: bool, x: u32) u32 {
    return twice(if (sq) &square else &double, x);
}

noinline fn viaMemory(p: *Unary, x: u32) u32 {
    const before = p.*(x);
    p.* = &double;
    return before +% p.*(x);
}

export fn memoryCaller(x: u32) u32 {
    var s: Unary = &succ;
    return viaMemory(&s, x);
}

test "indirect calls resolve through the address-taken functions" {
    for ([_]u32{ 0, 3, 255, 0xffffffff }) |n| {
        try std.testing.expectEqual(n *% 2, viaTable(0, n));
        try std.testing.expectEqual(n +% 1, viaTable(1, n));
        try std.testing.expectEqual(n *% n, viaTable(5, n));
        try std.testing.expectEqual(n +% 1, viaGlobal(false, n));
        try std.testing.expectEqual(n *% n, viaGlobal(true, n));
        try std.testing.expectEqual((n *% n) +% 4, fieldCaller(n));
        try std.testing.expectEqual((n *% n) *% (n *% n), viaParam(true, n));
        try std.testing.expectEqual(n *% 4, viaParam(false, n));
        try std.testing.expectEqual((n +% 1) +% (n *% 2), memoryCaller(n));
    }
}
