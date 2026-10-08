const std = @import("std");
const Pair = struct { x: u32, y: u32 };
const Outer = struct { tag: u32, inner: Pair };

export fn direct(input: u32) u32 {
    var pair = Pair{ .x = input, .y = 9 };
    const xp = &pair.x;
    const p: *Pair = @fieldParentPtr("x", xp);
    p.y = 12;
    return pair.x +% pair.y;
}

export fn nested(input: u32) u32 {
    var outer = Outer{ .tag = 5, .inner = .{ .x = input, .y = 9 } };
    const yp = &outer.inner.y;
    const inner: *Pair = @fieldParentPtr("y", yp);
    const p: *Outer = @fieldParentPtr("inner", inner);
    inner.x +%= 2;
    p.tag = 7;
    return outer.tag +% outer.inner.x +% yp.*;
}

export fn castAlias(input: u32) u32 {
    var pair = Pair{ .x = input, .y = 9 };
    const xp: *const u32 = &pair.x;
    const p: *const Pair = @fieldParentPtr("x", xp);
    @constCast(p).y = 33;
    return pair.x +% pair.y;
}

noinline fn write(p: *Pair) void {
    p.y = 42;
}

export fn escaped(input: u32) u32 {
    var pair = Pair{ .x = input, .y = 9 };
    const p: *Pair = @fieldParentPtr("x", &pair.x);
    write(p);
    return pair.x +% pair.y;
}

const Bag = struct { tag: u32, items: [2]Pair };

/// L11: a field of an array element inside a struct; both recoveries alias `bag`.
export fn arrayItem(input: u32, i: u32) u32 {
    var bag = Bag{ .tag = 1, .items = .{ .{ .x = 3, .y = 9 }, .{ .x = input, .y = 5 } } };
    const yp = &bag.items[i % 2].y;
    const item: *Pair = @fieldParentPtr("y", yp);
    item.x +%= 27;
    const outer: *Bag = @fieldParentPtr("items", &bag.items);
    outer.tag = 6;
    return bag.tag +% bag.items[i % 2].x +% yp.*;
}

test "local parent writes alias their original local" {
    for ([_]u32{ 0, 3, 255, 0xffffffff }) |n| {
        try std.testing.expectEqual(n +% 12, direct(n));
        try std.testing.expectEqual(n +% 18, nested(n));
        try std.testing.expectEqual(n +% 33, castAlias(n));
        try std.testing.expectEqual(n +% 42, escaped(n));
        try std.testing.expectEqual(6 +% (n +% 27) +% 5, arrayItem(n, 1));
        try std.testing.expectEqual(6 +% 30 +% 9, arrayItem(n, 0));
    }
}
