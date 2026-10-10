const std = @import("std");

const Mode = enum(u2) { off, low, high };
const Inner = packed struct(u12) { b: u4, c: u8 };
const Reg = packed struct(u24) { a: u4, inner: Inner, s: i5, on: bool, mode: Mode };
const Word = packed union { reg: Reg, raw: u24 };

var reg: Reg = undefined;
var word: Word = undefined;
var inner_g: Inner = undefined;

pub fn setA() u4 {
    reg.a = 5;
    return reg.a;
}
pub fn innerC() u8 {
    reg.a = 1;
    reg.inner.c = 0xAB;
    return reg.inner.c;
}
pub fn innerCKeepsA() u4 {
    reg.a = 1;
    reg.inner.c = 0xAB;
    return reg.a;
}
pub fn setInner() Inner {
    reg.inner = .{ .b = 2, .c = 0x5A };
    return reg.inner;
}
pub fn innerPartial() Inner {
    reg.inner.c = 0x5A;
    return reg.inner;
}
pub fn undefKeepsA() u4 {
    reg.a = 3;
    reg.inner.b = undefined;
    return reg.a;
}
pub fn undefField() u4 {
    reg.inner.b = 7;
    reg.inner.b = undefined;
    return reg.inner.b;
}
pub fn signedS() i5 {
    reg.s = -3;
    return reg.s;
}
pub fn boolOn() bool {
    reg.on = true;
    return reg.on;
}
pub fn modeHigh() Mode {
    reg.mode = .high;
    return reg.mode;
}
pub fn unionRaw() u24 {
    word.raw = 0x123456;
    word.reg.a = 0xF;
    return word.raw;
}
pub fn unionBadMode() Mode {
    word.raw = 0xC00000;
    return word.reg.mode;
}
pub fn hostAbi() u4 {
    reg.a = 9;
    reg.inner = .{ .b = 1, .c = 2 };
    return reg.a;
}
// Through a runtime pointer the compiler cannot fold the field pointers: it emits
// `struct_field_ptr_index_N` instructions with computed pointer types.
pub fn innerCPtr(r: *Reg) u8 {
    r.a = 1;
    r.inner.c = 0xAB;
    return r.inner.c;
}
pub fn innerCKeepsAPtr(r: *Reg) u4 {
    r.a = 1;
    r.inner.c = 0xAB;
    return r.a;
}
pub fn setInnerPtr(r: *Reg) Inner {
    r.inner = .{ .b = 2, .c = 0x5A };
    return r.inner;
}
pub fn bytePtr() u8 {
    inner_g.b = 1;
    inner_g.c = 0xCD;
    return inner_g.c;
}
pub fn localUndef() u4 {
    var r: Reg = undefined;
    r.a = 6;
    r.inner.b = undefined;
    return r.a;
}

test "bit-pointer stores keep the other bits of the host" {
    try std.testing.expectEqual(@as(u4, 5), setA());
    try std.testing.expectEqual(@as(u8, 0xAB), innerC());
    try std.testing.expectEqual(@as(u4, 1), innerCKeepsA());
    const inner = setInner();
    try std.testing.expectEqual(@as(u4, 2), inner.b);
    try std.testing.expectEqual(@as(u8, 0x5A), inner.c);
    try std.testing.expectEqual(@as(u12, 0x5A2), @as(u12, @bitCast(inner)));
    try std.testing.expectEqual(@as(u4, 3), undefKeepsA());
}

test "signed, bool and enum fields" {
    try std.testing.expectEqual(@as(i5, -3), signedS());
    try std.testing.expect(boolOn());
    try std.testing.expectEqual(Mode.high, modeHigh());
}

test "runtime pointer to the packed register" {
    var r: Reg = undefined;
    try std.testing.expectEqual(@as(u8, 0xAB), innerCPtr(&r));
    try std.testing.expectEqual(@as(u4, 1), innerCKeepsAPtr(&r));
    const inner = setInnerPtr(&r);
    try std.testing.expectEqual(@as(u12, 0x5A2), @as(u12, @bitCast(inner)));
}

test "packed union overlay and stack local" {
    try std.testing.expectEqual(@as(u8, 0xCD), bytePtr());
    try std.testing.expectEqual(@as(u24, 0x12345F), unionRaw());
    try std.testing.expectEqual(@as(u4, 6), localUndef());
    try std.testing.expectEqual(@as(u4, 9), hostAbi());
}
// Not run natively: innerPartial and undefField read bits that are still undefined, and
// unionBadMode loads an enum tag without a name (a safety panic).

comptime {
    _ = &setA;
    _ = &innerC;
    _ = &innerCKeepsA;
    _ = &setInner;
    _ = &innerPartial;
    _ = &undefKeepsA;
    _ = &undefField;
    _ = &signedS;
    _ = &boolOn;
    _ = &modeHigh;
    _ = &unionRaw;
    _ = &unionBadMode;
    _ = &hostAbi;
    _ = &localUndef;
    _ = &bytePtr;
    _ = &innerCPtr;
    _ = &innerCKeepsAPtr;
    _ = &setInnerPtr;
}
