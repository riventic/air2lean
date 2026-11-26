//! L04: the alias and cleanup paths of pointer try for every payload shape, not only `u8`
//! (`README.md`): integers of two, four and eight bytes, a struct, an error union whose error
//! set is `anyerror`, and an alias cast to another element type of the same size. Each function
//! is the one-byte function of `../try_pointers.zig` or `../try_aliases.zig` with the payload
//! type changed.
const std = @import("std");
pub const Failure = error{ Bad, Other };
pub const Pair = extern struct { a: u32, b: u16 };

// Two pointer-try results of one union alias: the write through the first is read through the
// second.

pub fn writeAlias16(cell: *Failure!u16, value: u16) Failure!u16 {
    const p = &(try cell.*);
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

pub fn writeAlias32(cell: *Failure!u32, value: u32) Failure!u32 {
    const p = &(try cell.*);
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

pub fn writeAlias64(cell: *Failure!u64, value: u64) Failure!u64 {
    const p = &(try cell.*);
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

pub fn writeAliasPair(cell: *Failure!Pair, value: Pair) Failure!Pair {
    const p = &(try cell.*);
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

pub fn writeAliasAny(cell: *anyerror!u32, value: u32) anyerror!u32 {
    const p = &(try cell.*);
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

/// The first alias is cast to another element type of the same size.
pub fn writeAliasSigned(cell: *Failure!u16, value: i16) Failure!u16 {
    const p: *i16 = @ptrCast(&(try cell.*));
    const q = &(try cell.*);
    p.* = value;
    return q.*;
}

// `defer` and `errdefer` around a pointer try: the result is read before the cleanup runs.

pub fn cleanup16(cell: *Failure!u16, ordinary: *u32, on_error: *u32) Failure!u16 {
    defer ordinary.* += 1;
    errdefer on_error.* += 1;
    const p = &(try cell.*);
    return p.*;
}

pub fn cleanup32(cell: *Failure!u32, ordinary: *u32, on_error: *u32) Failure!u32 {
    defer ordinary.* += 1;
    errdefer on_error.* += 1;
    const p = &(try cell.*);
    return p.*;
}

pub fn cleanup64(cell: *Failure!u64, ordinary: *u32, on_error: *u32) Failure!u64 {
    defer ordinary.* += 1;
    errdefer on_error.* += 1;
    const p = &(try cell.*);
    return p.*;
}

pub fn cleanupPair(cell: *Failure!Pair, ordinary: *u32, on_error: *u32) Failure!Pair {
    defer ordinary.* += 1;
    errdefer on_error.* += 1;
    const p = &(try cell.*);
    return p.*;
}

pub fn cleanupAny(cell: *anyerror!u32, ordinary: *u32, on_error: *u32) anyerror!u32 {
    defer ordinary.* += 1;
    errdefer on_error.* += 1;
    const p = &(try cell.*);
    return p.*;
}

// `errdefer` rewrites the whole addressed union after the pointer try captured the error.

pub fn resetOnError16(cell: *Failure!u16, fallback: u16) Failure!*u16 {
    errdefer cell.* = fallback;
    return &(try cell.*);
}

pub fn resetOnError32(cell: *Failure!u32, fallback: u32) Failure!*u32 {
    errdefer cell.* = fallback;
    return &(try cell.*);
}

pub fn resetOnError64(cell: *Failure!u64, fallback: u64) Failure!*u64 {
    errdefer cell.* = fallback;
    return &(try cell.*);
}

pub fn resetOnErrorPair(cell: *Failure!Pair, fallback: Pair) Failure!*Pair {
    errdefer cell.* = fallback;
    return &(try cell.*);
}

comptime {
    _ = &writeAlias16;
    _ = &writeAlias32;
    _ = &writeAlias64;
    _ = &writeAliasPair;
    _ = &writeAliasAny;
    _ = &writeAliasSigned;
    _ = &cleanup16;
    _ = &cleanup32;
    _ = &cleanup64;
    _ = &cleanupPair;
    _ = &cleanupAny;
    _ = &resetOnError16;
    _ = &resetOnError32;
    _ = &resetOnError64;
    _ = &resetOnErrorPair;
}

fn expectAlias(comptime T: type, comptime f: anytype, first: T, second: T) !void {
    var a: Failure!T = first;
    try std.testing.expectEqual(second, try f(&a, second));
    try std.testing.expectEqual(second, try a);
    a = error.Other;
    try std.testing.expectError(error.Other, f(&a, second));
    try std.testing.expectError(error.Other, a);
}

test "two captures alias for every payload width" {
    try expectAlias(u16, writeAlias16, 0x0102, 0xa1b2);
    try expectAlias(u32, writeAlias32, 0x01020304, 0xa1b2c3d4);
    try expectAlias(u64, writeAlias64, 0x0102030405060708, 0xa1b2c3d4e5f60718);
    try expectAlias(Pair, writeAliasPair, .{ .a = 0x01020304, .b = 0x0506 }, .{ .a = 0xa1b2c3d4, .b = 0xe5f6 });
}

test "two captures alias under anyerror" {
    var a: anyerror!u32 = 0x01020304;
    try std.testing.expectEqual(@as(u32, 0xa1b2c3d4), try writeAliasAny(&a, 0xa1b2c3d4));
    try std.testing.expectEqual(@as(u32, 0xa1b2c3d4), try a);
    a = error.Other;
    try std.testing.expectError(error.Other, writeAliasAny(&a, 5));
    try std.testing.expectError(error.Other, a);
}

test "an alias cast to a signed element type" {
    var a: Failure!u16 = 0x0102;
    try std.testing.expectEqual(@as(u16, 0xfffe), try writeAliasSigned(&a, -2));
    try std.testing.expectEqual(@as(u16, 0xfffe), try a);
    a = error.Other;
    try std.testing.expectError(error.Other, writeAliasSigned(&a, -2));
    try std.testing.expectError(error.Other, a);
}

fn expectCleanup(comptime T: type, comptime E: type, comptime f: anytype, value: T) !void {
    var a: E!T = value;
    var ordinary: u32 = 0;
    var on_error: u32 = 0;
    try std.testing.expectEqual(value, try f(&a, &ordinary, &on_error));
    try std.testing.expectEqual(@as(u32, 1), ordinary);
    try std.testing.expectEqual(@as(u32, 0), on_error);
    a = error.Bad;
    try std.testing.expectError(error.Bad, f(&a, &ordinary, &on_error));
    try std.testing.expectEqual(@as(u32, 2), ordinary);
    try std.testing.expectEqual(@as(u32, 1), on_error);
    try std.testing.expectError(error.Bad, a);
    // One counter for both cleanup pointers: once on success, twice on error.
    var counter: u32 = 0;
    a = value;
    try std.testing.expectEqual(value, try f(&a, &counter, &counter));
    try std.testing.expectEqual(@as(u32, 1), counter);
    a = error.Bad;
    try std.testing.expectError(error.Bad, f(&a, &counter, &counter));
    try std.testing.expectEqual(@as(u32, 3), counter);
}

test "defer and errdefer for every payload width" {
    try expectCleanup(u16, Failure, cleanup16, 0x0102);
    try expectCleanup(u32, Failure, cleanup32, 0x01020304);
    try expectCleanup(u64, Failure, cleanup64, 0x0102030405060708);
    try expectCleanup(Pair, Failure, cleanupPair, .{ .a = 0x01020304, .b = 0x0506 });
    try expectCleanup(u32, anyerror, cleanupAny, 0x01020304);
}

fn expectReset(comptime T: type, comptime f: anytype, value: T, fallback: T) !void {
    var a: Failure!T = value;
    const p = try f(&a, fallback);
    try std.testing.expect(p == &(a catch unreachable));
    try std.testing.expectEqual(value, try a);
    a = error.Bad;
    try std.testing.expectError(error.Bad, f(&a, fallback));
    try std.testing.expectEqual(fallback, try a);
}

test "errdefer rewrites the addressed union for every payload width" {
    try expectReset(u16, resetOnError16, 0x0102, 0xa1b2);
    try expectReset(u32, resetOnError32, 0x01020304, 0xa1b2c3d4);
    try expectReset(u64, resetOnError64, 0x0102030405060708, 0xa1b2c3d4e5f60718);
    try expectReset(Pair, resetOnErrorPair, .{ .a = 0x01020304, .b = 0x0506 }, .{ .a = 0xa1b2c3d4, .b = 0xe5f6 });
}
