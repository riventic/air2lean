// Comptime-resolved locals: Sema moves the value of a `const` local whose address is taken
// into a constant global and leaves the local's dead `alloc` and stores as `bitcast`s of
// address 0 (Q01 heavy differential seeds 18, 19 and 39). See README.md.
const std = @import("std");

const U = union(enum) { a: u32, b: i32 };
// The fuzz case's union, used only by the pointer-free `dead`.
const F = union(enum) { a: u32, b: i32 };

noinline fn read(p: *const U, x: u32) u32 {
    return switch (p.*) {
        .a => |v| v +% x,
        .b => |v| @as(u32, @bitCast(v)) +% x,
    };
}

noinline fn bump(p: *u32) void {
    p.* +%= 1;
}

// The shrunk fuzz case (`tests/roadmap/fuzz` seed 19): only dead placeholders refer to the
// local. `dead` stays pointer-free, but `mem0` holds its constant.
pub fn dead(p0: u32, p1: u32) u32 {
    _ = p0;
    _ = p1;
    const un5: F = .{ .b = @as(i32, 0) };
    _ = un5;
    return @as(u32, 0);
}

// A live pointer to the local is a pointer to its constant global.
pub fn live(p0: u32) u32 {
    const un: U = .{ .b = @as(i32, -7) };
    return read(&un, p0);
}

// A function with a stack block.
pub fn stack(p0: u32) u32 {
    var x: u32 = p0;
    bump(&x);
    return x;
}

// `@ptrFromInt` in an otherwise pointer-free function.
pub fn roundTrip(a: usize) usize {
    const p: *u32 = @ptrFromInt(a | 4);
    return @intFromPtr(p) +% 1;
}

pub fn entry(a: u32, b: u32) u32 {
    return dead(a, b) +% live(a) +% stack(b);
}

comptime {
    _ = &entry;
    _ = &roundTrip;
}

test "native results" {
    try std.testing.expectEqual(@as(u32, 0), dead(5, 9));
    try std.testing.expectEqual(@as(u32, 4294967294), live(5));
    try std.testing.expectEqual(@as(u32, 10), stack(9));
    try std.testing.expectEqual(@as(u32, 8), entry(5, 9));
    try std.testing.expectEqual(@as(usize, 13), roundTrip(8));
}
