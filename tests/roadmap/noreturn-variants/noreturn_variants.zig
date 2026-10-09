//! Tagged unions with a `noreturn` variant (spike blocker B1): the variant is never active.
//! Exported with the patched 0.16.0 and 0.15.2 compilers (README.md); `native.zig` runs the
//! same functions natively.
const std = @import("std");

/// A `noreturn` variant between two inhabited ones.
pub const U = union(enum) { a: u8, b: noreturn, c: u32 };

/// Explicit, non-contiguous tag values: the translation keeps them.
pub const Kind = enum(u8) { x = 3, gone = 7, y = 9 };
pub const V = union(Kind) { x: u16, gone: noreturn, y: void };

/// The `noreturn` variant first, a one-bit tag and one inhabited variant (`std.testing.Smith`).
pub const One = union(enum(u1)) { never: noreturn, only: u16 };

/// `std.Io.Terminal.Mode` (0.16.0; `windows_api: noreturn` off Windows), or the same shape.
pub const Mode = if (@hasDecl(std.Io, "Terminal"))
    std.Io.Terminal.Mode
else
    union(enum) { no_color, escape_codes, windows_api: noreturn };

/// `Mode` in memory, after a field (`Io.Threaded.stderr_mode`).
pub const Holder = struct { mode: Mode, n: u32 };

pub fn get(u: U) u32 {
    return switch (u) {
        .a => |x| x,
        .b => unreachable,
        .c => |y| y,
    };
}

pub fn mk(x: u8) U {
    return .{ .a = x };
}

/// A local union: `a`, then `c`.
pub fn roundTrip(x: u8) u32 {
    var u: U = mk(x);
    const p = &u;
    p.* = .{ .c = @as(u32, x) + 1 };
    return get(p.*);
}

fn bump(p: *U) void {
    // Read first: `p.* = .{ .c = get(p.*) + 1 }` would set the tag before the read.
    const next = get(p.*) + 1;
    p.* = .{ .c = next };
}

fn readU(p: *const U) u32 {
    return get(p.*);
}

/// `U` in memory (tag at byte 4, payload at byte 0).
pub fn memRoundTrip(x: u8) u32 {
    var u: U = mk(x);
    bump(&u);
    bump(&u);
    return readU(&u);
}

pub fn mkV(n: u16) V {
    return if (n == 0) .y else .{ .x = n };
}

pub fn vValue(v: V) u16 {
    return switch (v) {
        .x => |n| n,
        .gone => unreachable,
        .y => 0,
    };
}

pub fn vTag(n: u16) u8 {
    return @intFromEnum(@as(Kind, mkV(n)));
}

fn readV(p: *const V) u16 {
    return vValue(p.*);
}

/// `V` in memory (payload at byte 0, tag at byte 2).
pub fn memV(n: u16) u16 {
    var v = mkV(n);
    return readV(&v);
}

pub fn oneValue(o: One) u16 {
    return switch (o) {
        .never => unreachable,
        .only => |n| n,
    };
}

pub fn oneRoundTrip(n: u16) u16 {
    const o: One = .{ .only = n };
    return oneValue(o);
}

pub fn isColor(m: Mode) bool {
    return switch (m) {
        .escape_codes => true,
        else => false,
    };
}

pub fn colorOf(code: u8) bool {
    const m: Mode = if (code == 1) .escape_codes else .no_color;
    return isColor(m);
}

fn holderColor(h: *const Holder) bool {
    return isColor(h.mode);
}

fn setMode(h: *Holder, color: bool) void {
    h.mode = if (color) .escape_codes else .no_color;
}

/// `Holder` in memory: `n + 1` with color, `n` without.
pub fn holderRoundTrip(color: bool, n: u32) u32 {
    var h: Holder = .{ .mode = .no_color, .n = n };
    setMode(&h, color);
    return if (holderColor(&h)) h.n + 1 else h.n;
}

comptime {
    _ = &get;
    _ = &mk;
    _ = &roundTrip;
    _ = &memRoundTrip;
    _ = &mkV;
    _ = &vValue;
    _ = &vTag;
    _ = &memV;
    _ = &oneValue;
    _ = &oneRoundTrip;
    _ = &isColor;
    _ = &colorOf;
    _ = &holderRoundTrip;
}
