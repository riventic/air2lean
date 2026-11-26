//! Layouts of `extern` structs and unions that the checker compares with the C layout rule
//! (check.sh, test_cli.py, LayoutChecker.lean): fields in declaration order, each at its
//! predecessor's end rounded up to the field's alignment (its type's, or an explicit
//! `align(N)`), the size rounded up to the largest field alignment. Exported for wasm32 and
//! x86_64: `c_long`, `usize` and pointers change the offsets with the target.
const std = @import("std");

/// Natural alignments: 0, `@sizeOf(usize)`, `2 * @sizeOf(usize)`.
pub const Plain = extern struct { a: u8, p: *u32, n: c_long, t: u16 };

/// An under-aligned field: `b` directly after `a`.
pub const Under = extern struct { a: u8, b: u32 align(1), c: u16 };

/// An over-aligned field: `b` at 16, the struct aligned to 16.
pub const Over = extern struct { a: u8, b: u32 align(16) };

/// A zero-sized field takes no bytes but its alignment counts.
pub const Zero = extern struct { a: u8, z: [0]u32, b: u8 };

/// Nested `extern` structs and an array of them.
pub const Nested = extern struct { tag: u8, in: Under, pair: [2]Plain, last: u8 };

/// An `extern` union: the largest field rounded up to the largest alignment.
pub const Either = extern union { a: u8, b: u64, c: [3]u16, d: Under };

pub fn plainN(p: *const Plain) c_long {
    return p.n;
}
pub fn plainT(p: *const Plain) u16 {
    return p.t;
}
pub fn underB(p: *const Under) u32 {
    return p.b;
}
pub fn underC(p: *const Under) u16 {
    return p.c;
}
pub fn setUnderB(p: *Under, v: u32) void {
    p.b = v;
}
pub fn overB(p: *const Over) u32 {
    return p.b;
}
pub fn zeroB(p: *const Zero) u8 {
    return p.b;
}
pub fn nestedLast(p: *const Nested) u8 {
    return p.last;
}
pub fn nestedInB(p: *const Nested) u32 {
    return p.in.b;
}
pub fn nestedPairN(p: *const Nested, i: usize) c_long {
    return p.pair[i].n;
}
/// The whole struct through memory: the encoding of every field at its offset.
pub fn copyNested(dst: *Nested, src: *const Nested) void {
    dst.* = src.*;
}
pub fn eitherB(p: *const Either) u64 {
    return p.b;
}
pub fn eitherD(p: *const Either) u16 {
    return p.d.c;
}

// The layouts that the checker recomputes, evaluated by the compiler for the target.
comptime {
    const w = @sizeOf(usize);
    std.debug.assert(@offsetOf(Plain, "p") == w and @offsetOf(Plain, "n") == 2 * w);
    std.debug.assert(@offsetOf(Plain, "t") == 3 * w and @sizeOf(Plain) == 4 * w);
    std.debug.assert(@offsetOf(Under, "b") == 1 and @offsetOf(Under, "c") == 6);
    std.debug.assert(@sizeOf(Under) == 8 and @alignOf(Under) == 2);
    std.debug.assert(@offsetOf(Over, "b") == 16 and @sizeOf(Over) == 32 and @alignOf(Over) == 16);
    std.debug.assert(@offsetOf(Zero, "z") == 4 and @offsetOf(Zero, "b") == 4 and @sizeOf(Zero) == 8);
    std.debug.assert(@offsetOf(Nested, "in") == 2 and @offsetOf(Nested, "pair") == std.mem.alignForward(usize, 10, w));
    std.debug.assert(@sizeOf(Either) == 8 and @alignOf(Either) == 8);
}

comptime {
    _ = &plainN;
    _ = &plainT;
    _ = &underB;
    _ = &underC;
    _ = &setUnderB;
    _ = &overB;
    _ = &zeroB;
    _ = &nestedLast;
    _ = &nestedInB;
    _ = &nestedPairN;
    _ = &copyNested;
    _ = &eitherB;
    _ = &eitherD;
}
