//! L06 union-member constant pointer bases. Source of the compiler exports in air/<version>
//! (provenance.json): each returned constant pointer is based on a member of an `extern`,
//! tagged or bare union inside the global `table`. `zig test` checks the offsets that the
//! exports record against the compiled program (stage2_x86_64, x86_64-linux-musl, ReleaseSafe).
const std = @import("std");

pub const Failure = error{Bad};
pub const Pair = extern struct { lo: u16, hi: u16 };
/// Every member at byte 0 (Sema keeps the parent pointer).
pub const Ext = extern union { word: u32, pair: Pair, bytes: [4]u8 };
/// The tag first (alignment 4 ≥ 2): the payload at 4.
pub const Wide = union(enum(u32)) { none, half: u16, cells: [3]u16 };
/// The payload first (alignment 8 > 1): the payload at 0, the tag at 8.
pub const Low = union(enum) { wide: u64, pair: [2]u8 };
/// A bare union: in ReleaseSafe its hidden safety tag comes first, the payload at 1.
pub const Bare = union { byte: u8, pair: [2]u8 };
pub const Inner = struct { a: u8, bare: Bare };
/// A union member inside a struct inside a union payload (the `u64` tag first: payload at 8).
pub const Outer = union(enum(u64)) { inner: Inner, none };
pub const Holder = struct {
    head: u32,
    ext: Ext,
    wide: Wide,
    low: Low,
    bare: Bare,
    outer: Outer,
    maybe: ?Wide,
    res: Failure!Ext,
};

pub const table: Holder = .{
    .head = 1,
    .ext = .{ .bytes = .{ 0x11, 0x22, 0x33, 0x44 } },
    .wide = .{ .cells = .{ 100, 101, 102 } },
    .low = .{ .pair = .{ 30, 31 } },
    .bare = .{ .pair = .{ 40, 41 } },
    .outer = .{ .inner = .{ .a = 50, .bare = .{ .pair = .{ 51, 52 } } } },
    .maybe = .{ .cells = .{ 200, 201, 202 } },
    .res = .{ .word = 0x01020304 },
};

/// `extern` members: the union's own address, then an `extern` struct field / array element.
/// An `extern` member pointer needs only `table`'s type; reading `table.head` at comptime
/// resolves its value first, so the export carries the initializer.
pub fn extWordPtr() *const u32 {
    comptime std.debug.assert(table.head == 1);
    return &table.ext.word;
}
pub fn extHiPtr() *const u16 {
    comptime std.debug.assert(table.head == 1);
    return &table.ext.pair.hi;
}
pub fn extBytePtr() *const u8 {
    comptime std.debug.assert(table.head == 1);
    return &table.ext.bytes[2];
}
/// Tagged unions: tag first and payload first.
pub fn wideCellPtr() *const u16 {
    return &table.wide.cells[2];
}
pub fn wideSlice() []const u16 {
    return table.wide.cells[1..3];
}
pub fn lowPairPtr() *const u8 {
    return &table.low.pair[1];
}
/// Bare union (hidden safety tag) and a union member nested in a union payload.
pub fn barePairPtr() *const u8 {
    return &table.bare.pair[1];
}
pub fn outerPairPtr() *const u8 {
    return &table.outer.inner.bare.pair[1];
}
/// Union members under an optional and an error-union payload.
pub fn maybeCellPtr() *const u16 {
    return &table.maybe.?.cells[1];
}
pub fn resBytePtr() *const u8 {
    return &(table.res catch unreachable).bytes[3];
}
/// A union with an alignment-1 error-union payload member (`Failure![2]u8` at 4 + 2): on
/// `stage2_llvm` the translator rejects a constant at or one past that payload (6..8) through
/// any member, and accepts the others.
pub const Mixed = union(enum(u32)) { res: Failure![2]u8, raw: [4]u8 };
pub const mixed: Mixed = .{ .raw = .{ 60, 61, 62, 63 } };
pub fn mixedLowPtr() *const u8 {
    return &mixed.raw[1];
}
pub fn mixedHighPtr() *const u8 {
    return &mixed.raw[3];
}
/// Reads through a union-member constant at a run-time index (not folded by Sema).
pub fn readWideCell(i: usize) u16 {
    const cells = &table.wide.cells;
    return cells[i];
}
pub fn readExtByte(i: usize) u8 {
    const bytes = &table.ext.bytes;
    return bytes[i];
}
/// The same projections at run time from a `*const Holder` (ReleaseSafe checks the tags).
pub fn projectWide(h: *const Holder) *const u16 {
    return &h.wide.cells[2];
}
pub fn projectBare(h: *const Holder) *const u8 {
    return &h.bare.pair[1];
}

noinline fn launder(comptime T: type, p: *const T) *const T {
    const q: *const volatile *const T = &p;
    return q.*;
}

test "union-member constant bases retain identity and offsets" {
    const base = @intFromPtr(&table);
    const ext = base + @offsetOf(Holder, "ext");
    try std.testing.expectEqual(ext, @intFromPtr(launder(u32, extWordPtr())));
    try std.testing.expectEqual(ext + 2, @intFromPtr(launder(u16, extHiPtr())));
    try std.testing.expectEqual(ext + 2, @intFromPtr(launder(u8, extBytePtr())));
    const wide = base + @offsetOf(Holder, "wide");
    try std.testing.expectEqual(wide + 4 + 4, @intFromPtr(launder(u16, wideCellPtr())));
    try std.testing.expectEqual(wide + 4 + 2, @intFromPtr(wideSlice().ptr));
    try std.testing.expectEqual(@as(usize, 2), wideSlice().len);
    try std.testing.expectEqual(base + @offsetOf(Holder, "low") + 1, @intFromPtr(launder(u8, lowPairPtr())));
    try std.testing.expectEqual(base + @offsetOf(Holder, "bare") + 1 + 1, @intFromPtr(launder(u8, barePairPtr())));
    try std.testing.expectEqual(
        base + @offsetOf(Holder, "outer") + 8 + @offsetOf(Inner, "bare") + 1 + 1,
        @intFromPtr(launder(u8, outerPairPtr())),
    );
    try std.testing.expectEqual(base + @offsetOf(Holder, "maybe") + 4 + 2, @intFromPtr(launder(u16, maybeCellPtr())));
    try std.testing.expectEqual(base + @offsetOf(Holder, "res") + 3, @intFromPtr(launder(u8, resBytePtr())));
    try std.testing.expectEqual(projectWide(&table), launder(u16, wideCellPtr()));
    try std.testing.expectEqual(projectBare(&table), launder(u8, barePairPtr()));
    try std.testing.expectEqual(@as(u16, 102), launder(u16, wideCellPtr()).*);
    try std.testing.expectEqual(@as(u16, 0x4433), launder(u16, extHiPtr()).*);
    try std.testing.expectEqual(@as(u8, 41), launder(u8, barePairPtr()).*);
    try std.testing.expectEqual(@as(u8, 52), launder(u8, outerPairPtr()).*);
    try std.testing.expectEqual(@as(u16, 101), readWideCell(1));
    try std.testing.expectEqual(@as(u8, 0x33), readExtByte(2));
    try std.testing.expectEqual(@intFromPtr(&mixed) + 4 + 1, @intFromPtr(launder(u8, mixedLowPtr())));
    try std.testing.expectEqual(@intFromPtr(&mixed) + 4 + 3, @intFromPtr(launder(u8, mixedHighPtr())));
    try std.testing.expectEqual(@as(u8, 63), launder(u8, mixedHighPtr()).*);
}

// The layout that the exports and proofs record (x86_64).
comptime {
    std.debug.assert(@sizeOf(Ext) == 4 and @alignOf(Ext) == 4);
    std.debug.assert(@sizeOf(Wide) == 12 and @alignOf(Wide) == 4);
    std.debug.assert(@sizeOf(Low) == 16 and @alignOf(Low) == 8);
    std.debug.assert(@sizeOf(Outer) == 16 and @alignOf(Outer) == 8);
    std.debug.assert(@sizeOf(Mixed) == 8 and @sizeOf(Failure![2]u8) == 4);
}

comptime {
    _ = &extWordPtr; _ = &extHiPtr; _ = &extBytePtr; _ = &wideCellPtr; _ = &wideSlice;
    _ = &lowPairPtr; _ = &barePairPtr; _ = &outerPairPtr; _ = &maybeCellPtr; _ = &resBytePtr;
    _ = &mixedLowPtr; _ = &mixedHighPtr; _ = &readWideCell; _ = &readExtByte;
    _ = &projectWide; _ = &projectBare;
}
