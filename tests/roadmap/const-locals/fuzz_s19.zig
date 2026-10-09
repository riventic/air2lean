// Q01 heavy differential, seeds 18, 19 and 39 (shrunk from seed 19): a comptime-known tagged-union
// local whose address is taken becomes a constant global, and Sema leaves `bitcast`s of address 0
// for its dead `alloc` and stores. The translation emitted them as `Zig.ptrFromAddr 0` in a
// pointer-free function, and (when another function used memory) encoded the constant without a
// `Zig.Enc U` instance; it did not elaborate. Fixed: the dead placeholders are dropped and every
// global's type is encodable (README.md). Native: `entry` returns 0.
const U = union(enum) { a: u32, b: i32 };

fn work(p0: u32, p1: u32) u32 {
    _ = p0;
    _ = p1;
    const un5: U = .{ .b = @as(i32, 0) };
    _ = un5;
    return @as(u32, 0);
}

pub fn entry(a: u32, b: u32) u32 {
    return work(a, b);
}

comptime {
    _ = &entry;
}

test "native result" {
    try @import("std").testing.expectEqual(@as(u32, 0), entry(3, 4));
}
