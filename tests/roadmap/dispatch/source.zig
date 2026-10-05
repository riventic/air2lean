//! Source-native qualification of labelled switches; no test-only AIR edits.
const std = @import("std");

export fn walk(n: u8, base: u8) u8 {
    var total = base;
    return sw: switch (n) {
        0 => total,
        else => |value| {
            total +%= value;
            continue :sw value - 1;
        },
    };
}

export fn nested(mode: u8, n: u8) u8 {
    return outer: switch (mode) {
        0 => inner: switch (n) {
            0 => continue :outer 1,
            1 => continue :outer 2,
            else => continue :inner 0,
        },
        1 => 77,
        2 => 88,
        else => 99,
    };
}

export fn fixedCapture(initial: u8) u8 {
    return sw: switch (initial) {
        0 => continue :sw 1,
        1 => initial,
        else => 9,
    };
}

export fn ranges(n: u8) u8 {
    return sw: switch (n) {
        2...5 => continue :sw 10,
        10 => 17,
        else => 23,
    };
}

const Status = enum(u8) { a, b, c };

export fn enumStep(initial: u8) u8 {
    const status: Status = @enumFromInt(initial);
    return sw: switch (status) {
        .a => continue :sw .b,
        .b => continue :sw .c,
        .c => 42,
    };
}

const Payload = union(enum) { count: u8, done: u8 };

export fn unionWalk(n: u8) u8 {
    return sw: switch (Payload{ .count = n }) {
        .count => |value| {
            if (value == 0) continue :sw .{ .done = 42 };
            continue :sw .{ .count = value - 1 };
        },
        .done => |value| value,
    };
}

test "dispatch selector, captures, ranges, nested target exits" {
    try std.testing.expectEqual(@as(u8, 42), enumStep(0));
    try std.testing.expectEqual(@as(u8, 42), enumStep(2));
    try std.testing.expectEqual(@as(u8, 42), unionWalk(7));
    try std.testing.expectEqual(@as(u8, 13), walk(3, 7));
    try std.testing.expectEqual(@as(u8, 128), walk(255, 0));
    try std.testing.expectEqual(@as(u8, 77), nested(0, 2));
    try std.testing.expectEqual(@as(u8, 88), nested(0, 1));
    try std.testing.expectEqual(@as(u8, 88), nested(2, 0));
    try std.testing.expectEqual(@as(u8, 0), fixedCapture(0));
    try std.testing.expectEqual(@as(u8, 17), ranges(2));
    try std.testing.expectEqual(@as(u8, 17), ranges(5));
    try std.testing.expectEqual(@as(u8, 23), ranges(6));
}
