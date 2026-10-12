//! L04: pointer try on a heap union that the cleanup frees, and payload pointers shared by
//! threads (`README.md`).
const std = @import("std");
pub const Failure = error{ Bad, Other };

fn readPayload(cell: *Failure!u8) Failure!u8 {
    const p = &(try cell.*);
    return p.*;
}

fn writePayload(cell: *Failure!u8, value: u8) Failure!void {
    const p = &(try cell.*);
    p.* = value;
}

/// The union lives on the heap; on error the `errdefer` cleanup frees it after the pointer try
/// has captured the error.
pub fn freeOnError(a: std.mem.Allocator, value: u8, fail: bool) (Failure || error{OutOfMemory})!u8 {
    const cell = try a.create(Failure!u8);
    cell.* = if (fail) error.Bad else value;
    errdefer a.destroy(cell);
    const p = &(try cell.*);
    const v = p.*;
    a.destroy(cell);
    return v;
}

/// The payload pointer outlives its union: `defer` frees the union before the caller reads.
fn danglingPayload(a: std.mem.Allocator, value: u8) (Failure || error{OutOfMemory})!*u8 {
    const cell = try a.create(Failure!u8);
    defer a.destroy(cell);
    cell.* = value;
    return &(try cell.*);
}

/// A use after free through the payload pointer (illegal behaviour; not run natively).
pub fn readDangling(a: std.mem.Allocator, value: u8) (Failure || error{OutOfMemory})!u8 {
    const p = try danglingPayload(a, value);
    return p.*;
}

fn reader(cell: *Failure!u8, out: *u8) void {
    out.* = readPayload(cell) catch 0;
}

fn writer(cell: *Failure!u8, value: u8) void {
    writePayload(cell, value) catch {};
}

/// Two threads take the payload pointer of one union and read through it: no race.
pub fn concurrentReads(value: u8, fail: bool) !u16 {
    var cell: Failure!u8 = if (fail) error.Other else value;
    var x: u8 = 1;
    var y: u8 = 1;
    const t1 = try std.Thread.spawn(.{}, reader, .{ &cell, &x });
    const t2 = try std.Thread.spawn(.{}, reader, .{ &cell, &y });
    t1.join();
    t2.join();
    return @as(u16, x) + y;
}

/// Two threads write through the payload pointers of two unions: disjoint, no race.
pub fn concurrentWrites(v1: u8, v2: u8) !u16 {
    var c1: Failure!u8 = 0;
    var c2: Failure!u8 = 0;
    const t1 = try std.Thread.spawn(.{}, writer, .{ &c1, v1 });
    const t2 = try std.Thread.spawn(.{}, writer, .{ &c2, v2 });
    t1.join();
    t2.join();
    return @as(u16, try c1) * 256 + (try c2);
}

/// One thread writes through the payload pointer while another reads it: a data race (illegal
/// behaviour; not run natively).
pub fn racingAliases(value: u8) !u8 {
    var cell: Failure!u8 = 0;
    var out: u8 = 0;
    const t1 = try std.Thread.spawn(.{}, writer, .{ &cell, value });
    const t2 = try std.Thread.spawn(.{}, reader, .{ &cell, &out });
    t1.join();
    t2.join();
    return out;
}

comptime {
    _ = &freeOnError;
    _ = &readDangling;
    _ = &concurrentReads;
    _ = &concurrentWrites;
    _ = &racingAliases;
}

test "the cleanup frees the union after the pointer try" {
    const a = std.testing.allocator;
    try std.testing.expectEqual(@as(u8, 7), try freeOnError(a, 7, false));
    try std.testing.expectError(error.Bad, freeOnError(a, 7, true));
}

test "payload pointers shared by threads" {
    try std.testing.expectEqual(@as(u16, 18), try concurrentReads(9, false));
    try std.testing.expectEqual(@as(u16, 0), try concurrentReads(9, true));
    try std.testing.expectEqual(@as(u16, 0x0304), try concurrentWrites(3, 4));
}
