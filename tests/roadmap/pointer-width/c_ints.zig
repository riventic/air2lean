//! T02: the C integer types and the pointer-sized integers under each profile. Exported for
//! wasm32-freestanding, wasm32-wasi (ILP32: `c_long`, `c_ulong`, `isize`, `usize` are 32 bits)
//! and x86_64-linux (LP64: 64 bits) by Zig 0.17.1 and 0.16.0 (exports.json). `c_char` is a
//! signed byte, `c_short`/`c_ushort` 16, `c_int`/`c_uint` 32 and `c_longlong`/`c_ulonglong` 64
//! bits on all three; `c_longlong` is 8-aligned on wasm32 too. `c_longdouble` is `f128` on wasm32
//! and `f80` on x86_64, 16 bytes with 16-byte alignment on both.
const std = @import("std");

// Checked increments: each overflows at its own type's maximum.
pub fn charSucc(n: c_char) c_char {
    return n + 1;
}
pub fn shortSucc(n: c_short) c_short {
    return n + 1;
}
pub fn ushortSucc(n: c_ushort) c_ushort {
    return n + 1;
}
pub fn intSucc(n: c_int) c_int {
    return n + 1;
}
pub fn uintSucc(n: c_uint) c_uint {
    return n + 1;
}
pub fn longSucc(n: c_long) c_long {
    return n + 1;
}
pub fn ulongSucc(n: c_ulong) c_ulong {
    return n + 1;
}
pub fn longlongSucc(n: c_longlong) c_longlong {
    return n + 1;
}
pub fn ulonglongSucc(n: c_ulonglong) c_ulonglong {
    return n + 1;
}
pub fn isizeSucc(n: isize) isize {
    return n + 1;
}

/// The product, or null when it does not fit a `c_ulong`.
pub fn ulongMul(a: c_ulong, b: c_ulong) ?c_ulong {
    const r = @mulWithOverflow(a, b);
    if (r[1] != 0) return null;
    return r[0];
}

/// Negation: overflows at the minimum of the target's `isize`.
pub fn isizeNeg(n: isize) isize {
    return -n;
}

/// Narrowing: the same width on wasm32 (never fails), a checked truncation on x86_64.
pub fn longToInt(n: c_long) c_int {
    return @intCast(n);
}

/// Widening: sign extension to the target's `c_long`.
pub fn intToLong(n: c_int) c_long {
    return n;
}

/// The two's complement reinterpretation.
pub fn longBits(n: c_long) c_ulong {
    return @bitCast(n);
}

/// `c_long` and a pointer-sized integer have the same width on both profiles.
pub fn longOfIsize(n: isize) c_long {
    return n;
}

/// `long double` addition (`f128` on wasm32, `f80` on x86_64).
pub fn ldAdd(a: c_longdouble, b: c_longdouble) c_longdouble {
    return a + b;
}

/// `{ int, long, short }`: 12 bytes (offsets 0/4/8) on wasm32, 24 (0/8/16) on x86_64.
pub const Rec = extern struct { a: c_int, b: c_long, c: c_short };

/// `{ char, long long, unsigned short, unsigned long }`: 24 bytes (0/8/16/20) on wasm32,
/// 32 (0/8/16/24) on x86_64.
pub const Mixed = extern struct { c: c_char, ll: c_longlong, us: c_ushort, ul: c_ulong };

/// `{ isize, usize }`: 8 bytes on wasm32, 16 on x86_64.
pub const Sizes = extern struct { i: isize, u: usize };

/// `{ char, long double }`: the `long double` at offset 16, 32 bytes on both.
pub const Ld = extern struct { tag: c_char, v: c_longdouble };

pub fn recB(r: *const Rec) c_long {
    return r.b;
}
pub fn recC(r: *const Rec) c_short {
    return r.c;
}
pub fn mixedUl(m: *const Mixed) c_ulong {
    return m.ul;
}
pub fn mixedLl(m: *const Mixed) c_longlong {
    return m.ll;
}
pub fn setMixedUs(m: *Mixed, v: c_ushort) void {
    m.us = v;
}
pub fn sizesU(s: *const Sizes) usize {
    return s.u;
}
pub fn ldV(p: *const Ld) c_longdouble {
    return p.v;
}

// The widths and layouts that the model checks, evaluated by the compiler for the target.
comptime {
    std.debug.assert(@bitSizeOf(c_char) == 8 and @bitSizeOf(c_short) == 16 and @bitSizeOf(c_ushort) == 16);
    std.debug.assert(@bitSizeOf(c_int) == 32 and @bitSizeOf(c_uint) == 32);
    std.debug.assert(@bitSizeOf(c_longlong) == 64 and @bitSizeOf(c_ulonglong) == 64);
    std.debug.assert(@bitSizeOf(c_long) == @bitSizeOf(usize) and @bitSizeOf(c_ulong) == @bitSizeOf(usize));
    std.debug.assert(@bitSizeOf(isize) == @bitSizeOf(usize) and @sizeOf(usize) == @sizeOf(*u8));
    std.debug.assert(@alignOf(c_longlong) == 8 and @alignOf(c_long) == @sizeOf(usize));
    std.debug.assert(@sizeOf(Rec) == 3 * @sizeOf(usize) and @offsetOf(Rec, "c") == 2 * @sizeOf(usize));
    std.debug.assert(@offsetOf(Mixed, "ll") == 8 and @offsetOf(Mixed, "ul") == 16 + @sizeOf(usize));
    std.debug.assert(@sizeOf(Mixed) == 16 + 2 * @sizeOf(usize));
    std.debug.assert(@sizeOf(Sizes) == 2 * @sizeOf(usize));
}

comptime {
    _ = &charSucc;
    _ = &shortSucc;
    _ = &ushortSucc;
    _ = &intSucc;
    _ = &uintSucc;
    _ = &longSucc;
    _ = &ulongSucc;
    _ = &longlongSucc;
    _ = &ulonglongSucc;
    _ = &isizeSucc;
    _ = &ulongMul;
    _ = &isizeNeg;
    _ = &longToInt;
    _ = &intToLong;
    _ = &longBits;
    _ = &longOfIsize;
    _ = &ldAdd;
    _ = &recB;
    _ = &recC;
    _ = &mixedUl;
    _ = &mixedLl;
    _ = &setMixedUs;
    _ = &sizesU;
    _ = &ldV;
}

const max = std.math.maxInt;

test "boundaries" {
    try std.testing.expectEqual(@as(c_char, 127), charSucc(126));
    try std.testing.expectEqual(@as(c_ushort, max(c_ushort)), ushortSucc(max(c_ushort) - 1));
    try std.testing.expectEqual(@as(c_long, max(c_long)), longSucc(max(c_long) - 1));
    try std.testing.expectEqual(@as(c_ulong, max(c_ulong)), ulongSucc(max(c_ulong) - 1));
    try std.testing.expectEqual(@as(isize, -max(isize)), isizeNeg(max(isize)));
    try std.testing.expectEqual(@as(?c_ulong, null), ulongMul(max(c_ulong) / 2 + 1, 2));
    try std.testing.expectEqual(@as(?c_ulong, max(c_ulong) - 1), ulongMul(max(c_ulong) / 2, 2));
    try std.testing.expectEqual(@as(c_int, -5), longToInt(-5));
    try std.testing.expectEqual(@as(c_long, std.math.minInt(c_int)), intToLong(std.math.minInt(c_int)));
    try std.testing.expectEqual(@as(c_ulong, max(c_ulong)), longBits(-1));
    try std.testing.expectEqual(@as(c_longdouble, 3.5), ldAdd(1.25, 2.25));
}

// The sizes and offsets are the comptime asserts above; the test reads the fields back.
test "layouts" {
    var m: Mixed = .{ .c = -1, .ll = 0, .us = 0, .ul = max(c_ulong) };
    setMixedUs(&m, 7);
    try std.testing.expectEqual(@as(c_ushort, 7), m.us);
    try std.testing.expectEqual(@as(c_ulong, max(c_ulong)), mixedUl(&m));
    m.ll = std.math.minInt(c_longlong);
    try std.testing.expectEqual(@as(c_longlong, std.math.minInt(c_longlong)), mixedLl(&m));
    const r: Rec = .{ .a = 1, .b = max(c_long), .c = -3 };
    try std.testing.expectEqual(@as(c_long, max(c_long)), recB(&r));
    try std.testing.expectEqual(@as(c_short, -3), recC(&r));
    const s: Sizes = .{ .i = -1, .u = max(usize) };
    try std.testing.expectEqual(@as(usize, max(usize)), sizesU(&s));
    const l: Ld = .{ .tag = 1, .v = 0.5 };
    try std.testing.expectEqual(@as(c_longdouble, 0.5), ldV(&l));
}
