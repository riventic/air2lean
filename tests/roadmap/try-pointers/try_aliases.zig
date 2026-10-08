const std = @import("std");
const base = @import("try_pointers.zig");
pub const Failure = base.Failure;

pub fn twoPaths(a: *Failure!u8, b: *Failure!u8, value: u8) Failure!u8 {
    const p = &(try a.*);
    const q = &(try b.*);
    p.* = value;
    return q.*;
}

pub fn resetOnError(cell: *Failure!u8, fallback: u8) Failure!*u8 {
    errdefer cell.* = fallback;
    return &(try cell.*);
}

comptime {
    _ = &twoPaths;
    _ = &resetOnError;
}

test "one union reached through two pointer paths" {
    var a: Failure!u8 = 7;
    try std.testing.expectEqual(@as(u8, 88), try twoPaths(&a, &a, 88));
    try std.testing.expectEqual(@as(u8, 88), try a);
    a = error.Other;
    try std.testing.expectError(error.Other, twoPaths(&a, &a, 88));
    try std.testing.expectError(error.Other, a);
}

test "distinct unions: write only the first, read only the second" {
    var a: Failure!u8 = 7;
    var b: Failure!u8 = 9;
    try std.testing.expectEqual(@as(u8, 9), try twoPaths(&a, &b, 88));
    try std.testing.expectEqual(@as(u8, 88), try a);
    try std.testing.expectEqual(@as(u8, 9), try b);
    a = 7;
    b = error.Bad;
    try std.testing.expectError(error.Bad, twoPaths(&a, &b, 88));
    try std.testing.expectEqual(@as(u8, 7), try a);
    try std.testing.expectError(error.Bad, b);
    a = error.Other;
    b = 9;
    try std.testing.expectError(error.Other, twoPaths(&a, &b, 88));
    try std.testing.expectEqual(@as(u8, 9), try b);
}

test "errdefer rewrites the addressed union after the error is captured" {
    var a: Failure!u8 = 5;
    const p = try resetOnError(&a, 42);
    try std.testing.expect(p == &(a catch unreachable));
    try std.testing.expectEqual(@as(u8, 5), try a);
    a = error.Bad;
    try std.testing.expectError(error.Bad, resetOnError(&a, 42));
    try std.testing.expectEqual(@as(u8, 42), try a);
}

test "one counter for both cleanup pointers" {
    var a: Failure!u8 = 9;
    var counter: u32 = 0;
    try std.testing.expectEqual(@as(u8, 9), try base.cleanup(&a, &counter, &counter));
    try std.testing.expectEqual(@as(u32, 1), counter);
    a = error.Bad;
    try std.testing.expectError(error.Bad, base.cleanup(&a, &counter, &counter));
    try std.testing.expectEqual(@as(u32, 3), counter);
}
