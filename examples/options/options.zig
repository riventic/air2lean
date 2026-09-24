//! Options: `find` returns `?usize`; `findOr` unwraps it with `orelse`; `firstIndexPlusOne`
//! unwraps it with `.?` (panics when the value is absent).

const std = @import("std");

/// First index of `x` in `xs`, or null.
pub fn find(xs: []const u32, x: u32) ?usize {
    for (xs, 0..) |v, i| {
        if (v == x) return i;
    }
    return null;
}

/// `find`, defaulting to `xs.len` when `x` is absent.
pub fn findOr(xs: []const u32, x: u32) usize {
    return find(xs, x) orelse xs.len;
}

/// `find(...) + 1`, unwrapped with `.?`. Panics when `x` is absent.
pub fn firstIndexPlusOne(xs: []const u32, x: u32) usize {
    return find(xs, x).? + 1;
}

comptime {
    _ = &find;
    _ = &findOr;
    _ = &firstIndexPlusOne;
}

test "find" {
    try std.testing.expectEqual(@as(?usize, 0), find(&.{ 1, 2, 3 }, 1));
    try std.testing.expectEqual(@as(?usize, 2), find(&.{ 1, 2, 3 }, 3));
    try std.testing.expectEqual(@as(?usize, null), find(&.{ 1, 2, 3 }, 9));
    try std.testing.expectEqual(@as(?usize, null), find(&.{}, 0));
}

test "findOr" {
    try std.testing.expectEqual(@as(usize, 1), findOr(&.{ 1, 2, 3 }, 2));
    try std.testing.expectEqual(@as(usize, 3), findOr(&.{ 1, 2, 3 }, 9));
    try std.testing.expectEqual(@as(usize, 0), findOr(&.{}, 0));
}

test "firstIndexPlusOne" {
    try std.testing.expectEqual(@as(usize, 1), firstIndexPlusOne(&.{ 1, 2, 3 }, 1));
    try std.testing.expectEqual(@as(usize, 3), firstIndexPlusOne(&.{ 1, 2, 3 }, 3));
    // Panics on an absent x (`.?` on null) — a trap, not a value, so not exercised here. See
    // tests/diff/options/inputs/firstIndexPlusOne.jsonl for that case.
}
