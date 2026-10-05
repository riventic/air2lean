const std = @import("std");
pub const Failure = error{Bad, Other};

pub fn payload8(cell: *Failure!u8) Failure!*u8 {
    return &(try cell.*);
}

pub fn payload64(cell: *Failure!u64) Failure!*u64 {
    return &(try cell.*);
}

pub fn writeAlias(cell: *Failure!u8, value: u8) Failure!u8 {
    const p = &(try cell.*);
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

pub fn cleanup(cell: *Failure!u8, ordinary: *u32, on_error: *u32) Failure!u8 {
    defer ordinary.* += 1;
    errdefer on_error.* += 1;
    const p = &(try cell.*);
    return p.*;
}

pub fn coldPayload(cell: *Failure!u8, on_error: *u32) Failure!*u8 {
    errdefer {
        if (true) {
            @branchHint(.cold);
            on_error.* += 1;
        }
    }
    return &(try cell.*);
}

test "payload address aliases original union across both layouts" {
    var a: Failure!u8 = 7;
    const p = try payload8(&a);
    p.* = 19;
    try std.testing.expectEqual(@as(u8, 19), try a);
    try std.testing.expect(p == &(a catch unreachable));
    var b: Failure!u64 = 41;
    const q = try payload64(&b);
    q.* = 123;
    try std.testing.expectEqual(@as(u64, 123), try b);
    try std.testing.expect(q == &(b catch unreachable));
}

test "two captures alias and error returns preserve original error" {
    var a: Failure!u8 = 7;
    try std.testing.expectEqual(@as(u8, 88), try writeAlias(&a, 88));
    try std.testing.expectEqual(@as(u8, 88), try a);
    a = error.Other;
    try std.testing.expectError(error.Other, writeAlias(&a, 88));
    try std.testing.expectError(error.Other, a);
}

test "defer errdefer and cold error body" {
    var a: Failure!u8 = 9;
    var ordinary: u32 = 0;
    var on_error: u32 = 0;
    try std.testing.expectEqual(@as(u8, 9), try cleanup(&a, &ordinary, &on_error));
    try std.testing.expectEqual(@as(u32, 1), ordinary);
    try std.testing.expectEqual(@as(u32, 0), on_error);
    a = error.Bad;
    try std.testing.expectError(error.Bad, cleanup(&a, &ordinary, &on_error));
    try std.testing.expectEqual(@as(u32, 2), ordinary);
    try std.testing.expectEqual(@as(u32, 1), on_error);
    try std.testing.expectError(error.Bad, coldPayload(&a, &on_error));
    try std.testing.expectEqual(@as(u32, 2), on_error);
}

comptime {
    _ = &payload8;
    _ = &payload64;
    _ = &writeAlias;
    _ = &cleanup;
    _ = &coldPayload;
}

test "address of undefined payload does not read its value" {
    var a: Failure!u8 = @as(u8, undefined);
    const p = try payload8(&a);
    p.* = 99;
    try std.testing.expectEqual(@as(u8, 99), try a);
    var b: Failure!u64 = @as(u64, undefined);
    const q = try payload64(&b);
    q.* = 123;
    try std.testing.expectEqual(@as(u64, 123), try b);
}
