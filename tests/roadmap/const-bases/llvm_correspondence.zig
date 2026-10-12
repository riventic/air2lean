//! L06: constant pointer bases against the backend that compiled them. Every base below is a
//! comptime-known pointer into `table`, lowered as a constant (`codegen.lowerPtr`), and compared
//! with the same projection computed at run time from a mutable copy (the model's offset). The
//! LLVM backend misplaces exactly the `eu_payload` constant of an alignment-1, nonzero-size payload
//! (README §LLVM); the translator rejects exactly that base on `stage2_llvm` and on a legacy
//! profile (llvm-check.sh). `zig test -fllvm` and `-fno-llvm` check both directions natively.
const std = @import("std");
const builtin = @import("builtin");

pub const Failure = error{Bad};
pub const Cell = struct { tag: u16, bytes: [4]u8 };
pub const Pair = extern union { word: u32, bytes: [4]u8 };
pub const Holder = struct {
    head: u64,
    maybe: ?Cell,
    res: Failure![3]u8,
    wide: Failure!u16,
    pair: Pair,
    tail: u32,
};
pub const table: Holder = .{
    .head = 1,
    .maybe = .{ .tag = 85, .bytes = .{ 10, 11, 12, 13 } },
    .res = .{ 20, 21, 22 },
    .wide = 0x3031,
    .pair = .{ .bytes = .{ 40, 41, 42, 43 } },
    .tail = 99,
};
var mutable: Holder = table;

/// Misplaced by LLVM: an element of an alignment-1 error-union payload.
pub fn resElem() *const u8 {
    return &(table.res catch unreachable)[2];
}
/// Agrees everywhere: the error code, an optional payload, an aligned payload, an extern union
/// member and a later field.
pub fn resCode() *const u8 {
    return @ptrCast(&table.res);
}
pub fn maybeElem() *const u8 {
    return &table.maybe.?.bytes[1];
}
pub fn widePayload() *const u16 {
    return &(table.wide catch unreachable);
}
pub fn pairByte() *const u8 {
    return &table.pair.bytes[2];
}
pub fn tailPtr() *const u32 {
    return &table.tail;
}

noinline fn launder(p: usize) usize {
    const q: *const volatile usize = &p;
    return q.*;
}
fn off(p: anytype, base: anytype) usize {
    return launder(@intFromPtr(p)) - @intFromPtr(base);
}

test "constant bases against the backend" {
    const m = &mutable;
    try std.testing.expectEqual(off(&(m.res catch unreachable)[2], m) != off(resElem(), &table),
        builtin.zig_backend == .stage2_llvm);
    try std.testing.expectEqual(off(@as(*const u8, @ptrCast(&m.res)), m), off(resCode(), &table));
    try std.testing.expectEqual(off(&m.maybe.?.bytes[1], m), off(maybeElem(), &table));
    try std.testing.expectEqual(off(&(m.wide catch unreachable), m), off(widePayload(), &table));
    try std.testing.expectEqual(off(&m.pair.bytes[2], m), off(pairByte(), &table));
    try std.testing.expectEqual(off(&m.tail, m), off(tailPtr(), &table));
}

comptime {
    _ = &resElem; _ = &resCode; _ = &maybeElem; _ = &widePayload; _ = &pairByte; _ = &tailPtr;
}
