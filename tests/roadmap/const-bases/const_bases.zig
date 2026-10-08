//! Source of the hand-written AIR in air/0.16.0 (exporter schema 12, stage2_x86_64,
//! x86_64-linux-musl baseline ReleaseSafe). Each exported constant pointer is a nested base:
//! an element of a payload of a field of a global, or a constant slice whose pointer is one.
//! `zig test` checks the offsets that the fixtures record against the compiled program.
const std = @import("std");

pub const Failure = error{Bad};
pub const Cell = struct { tag: u16, bytes: [4]u8 };
pub const Holder = struct { head: u64, maybe: ?Cell, res: Failure![3]u8, tail: u32 };
pub const table: Holder = .{
    .head = 1,
    .maybe = .{ .tag = 85, .bytes = .{ 10, 11, 12, 13 } },
    .res = .{ 20, 21, 22 },
    .tail = 99,
};

/// elem 2 of the eu_payload of field `res` (offset 20 + 2 + 2).
pub fn resElemPtr() *const u8 {
    return &(table.res catch unreachable)[2];
}
/// elem 1 of field `bytes` of the opt_payload of field `maybe` (offset 12 + 0 + 2 + 1).
pub fn maybeElemPtr() *const u8 {
    return &table.maybe.?.bytes[1];
}
/// The same byte through another projection chain.
pub fn maybeBytePtr() *const u8 {
    const bytes: [*]const u8 = @ptrCast(&table.maybe.?);
    return &bytes[3];
}
/// A constant slice whose pointer is the nested base above.
pub fn maybeSlice() []const u8 {
    return table.maybe.?.bytes[1..3];
}
/// The error union's first (code) byte: a field base only.
pub fn resCodePtr() *const u8 {
    return @ptrCast(&table.res);
}
/// A read through the nested constant pointer.
pub fn readResElem() u8 {
    return (&(table.res catch unreachable)[2]).*;
}
/// The same projections, computed at run time from the global's address.
pub fn projectRes(h: *const Holder) *const u8 {
    return &(h.res catch unreachable)[2];
}
pub fn projectMaybe(h: *const Holder) *const u8 {
    return &h.maybe.?.bytes[1];
}

noinline fn launder(p: *const u8) *const u8 {
    const q: *const volatile *const u8 = &p;
    return q.*;
}

test "nested constant bases retain identity and offsets (stage2_x86_64)" {
    const base = @intFromPtr(&table);
    try std.testing.expectEqual(base + 24, @intFromPtr(launder(resElemPtr())));
    try std.testing.expectEqual(base + 15, @intFromPtr(launder(maybeElemPtr())));
    try std.testing.expectEqual(maybeElemPtr(), maybeBytePtr());
    try std.testing.expectEqual(base + 15, @intFromPtr(maybeSlice().ptr));
    try std.testing.expectEqual(@as(usize, 2), maybeSlice().len);
    try std.testing.expectEqual(base + 20, @intFromPtr(resCodePtr()));
    try std.testing.expectEqual(projectRes(&table), launder(resElemPtr()));
    try std.testing.expectEqual(projectMaybe(&table), launder(maybeElemPtr()));
    try std.testing.expectEqual(@as(u8, 22), launder(resElemPtr()).*);
    try std.testing.expectEqual(@as(u8, 22), readResElem());
}

// The type-table layout that the hand-written fixtures record.
comptime {
    std.debug.assert(@sizeOf(Holder) == 32 and @alignOf(Holder) == 8);
    std.debug.assert(@offsetOf(Holder, "head") == 0 and @offsetOf(Holder, "tail") == 8);
    std.debug.assert(@offsetOf(Holder, "maybe") == 12 and @offsetOf(Holder, "res") == 20);
    std.debug.assert(@sizeOf(Cell) == 6 and @offsetOf(Cell, "bytes") == 2);
    std.debug.assert(@sizeOf(?Cell) == 8 and @sizeOf(Failure![3]u8) == 6);
}

comptime {
    _ = &resElemPtr; _ = &maybeElemPtr; _ = &maybeBytePtr; _ = &maybeSlice; _ = &resCodePtr;
    _ = &readResElem; _ = &projectRes; _ = &projectMaybe;
}
