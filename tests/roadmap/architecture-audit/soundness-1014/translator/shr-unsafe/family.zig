//! S3b sibling audit (docs/architecture-audit/soundness-2026-10-14.md, §S3), a manual probe that
//! no check runs: the integer safety checks with runtime safety on, each fed an input that
//! violates it. `CASE=<n> ./family` runs case n and prints the result when the check did not fire.
//! Inputs are loaded through volatile pointers, so nothing folds at compile time.
//!   zig build-exe -OReleaseSafe -lc family.zig        (aarch64-macos: 0.16.0, 0.17.0)
//!   zig build-exe -OReleaseSafe -lc -target aarch64-linux-musl family.zig   (0.14.1, 0.15.2)
//! In ReleaseSafe only the `@shrExact` exactness cases (1, 2, 3, 5) return a value; every other
//! case panics, in 0.14.1 to 0.17.0.
const std = @import("std");

extern "c" fn getenv(name: [*:0]const u8) ?[*:0]const u8;

var u_one: u32 = 1;
var u_three: u32 = 3;
var u_seven: u32 = 7;
var u_zero: u32 = 0;
var u_top: u32 = 0x80000000;
var i_neg3: i32 = -3;
var i_neg1: i32 = -1;
var i_zero: i32 = 0;
var i_min: i32 = std.math.minInt(i32);
var u24_one: u24 = 1;
var c1: u5 = 1;
var c24: u5 = 24;
var big: f64 = 1e10;
var nine: u8 = 9;

fn ld(comptime T: type, p: *T) T {
    return @as(*volatile T, p).*;
}

noinline fn shrExactU(a: u32, b: u5) u32 {
    return @shrExact(a, b);
}
noinline fn shrExactI(a: i32, b: u5) i32 {
    return @shrExact(a, b);
}
noinline fn shrExactV(a: @Vector(2, u32), b: @Vector(2, u5)) @Vector(2, u32) {
    return @shrExact(a, b);
}
noinline fn shrExact24(a: u24, b: u5) u24 {
    return @shrExact(a, b);
}
noinline fn shlExactU(a: u32, b: u5) u32 {
    return @shlExact(a, b);
}
noinline fn shlExactI(a: i32, b: u5) i32 {
    return @shlExact(a, b);
}
noinline fn shlExactV(a: @Vector(2, u32), b: @Vector(2, u5)) @Vector(2, u32) {
    return @shlExact(a, b);
}
noinline fn shlExact24(a: u24, b: u5) u24 {
    return @shlExact(a, b);
}
noinline fn shl24(a: u24, b: u5) u24 {
    return a << b;
}
noinline fn shr24(a: u24, b: u5) u24 {
    return a >> b;
}
noinline fn divExactU(a: u32, b: u32) u32 {
    return @divExact(a, b);
}
noinline fn divExactI(a: i32, b: i32) i32 {
    return @divExact(a, b);
}
noinline fn divTruncI(a: i32, b: i32) i32 {
    return @divTrunc(a, b);
}
noinline fn divFloorI(a: i32, b: i32) i32 {
    return @divFloor(a, b);
}
noinline fn divU(a: u32, b: u32) u32 {
    return a / b;
}
noinline fn remI(a: i32, b: i32) i32 {
    return @rem(a, b);
}
noinline fn modI(a: i32, b: i32) i32 {
    return @mod(a, b);
}
noinline fn addU(a: u32, b: u32) u32 {
    return a + b;
}
noinline fn subU(a: u32, b: u32) u32 {
    return a - b;
}
noinline fn mulI(a: i32, b: i32) i32 {
    return a * b;
}
noinline fn addV(a: @Vector(2, u32), b: @Vector(2, u32)) @Vector(2, u32) {
    return a + b;
}
noinline fn intCastU8(a: u32) u8 {
    return @intCast(a);
}
noinline fn intCastNeg(a: i32) u32 {
    return @intCast(a);
}
noinline fn intFromFloat(x: f64) i32 {
    return @intFromFloat(x);
}
const E = enum(u8) { a, b, c };
noinline fn enumFromInt(x: u8) E {
    return @enumFromInt(x);
}
noinline fn negI(a: i32) i32 {
    return -a;
}

pub fn main() void {
    const s = getenv("CASE") orelse return;
    const case = std.fmt.parseInt(u32, std.mem.span(s), 10) catch return;
    const p = std.debug.print;
    const one = ld(u5, &c1);
    const top = ld(u32, &u_top);
    const min = ld(i32, &i_min);
    const neg1 = ld(i32, &i_neg1);
    switch (case) {
        1 => p("shrExactU(3,1) = {d}\n", .{shrExactU(ld(u32, &u_three), one)}),
        2 => p("shrExactI(-3,1) = {d}\n", .{shrExactI(ld(i32, &i_neg3), one)}),
        3 => p("shrExactV({{3,4}},1) = {any}\n", .{shrExactV(.{ ld(u32, &u_three), 4 }, .{ one, one })}),
        4 => p("shrExact24(0,24) = {d}\n", .{shrExact24(0, ld(u5, &c24))}),
        5 => p("shrExact24(1,1) = {d}\n", .{shrExact24(ld(u24, &u24_one), one)}),
        6 => p("shlExactU(0x80000000,1) = {d}\n", .{shlExactU(top, one)}),
        7 => p("shlExactI(minInt,1) = {d}\n", .{shlExactI(min, one)}),
        8 => p("shlExactV({{0x80000000,1}},1) = {any}\n", .{shlExactV(.{ top, 1 }, .{ one, one })}),
        9 => p("shlExact24(0,24) = {d}\n", .{shlExact24(0, ld(u5, &c24))}),
        10 => p("shl24(1,24) = {d}\n", .{shl24(ld(u24, &u24_one), ld(u5, &c24))}),
        11 => p("shr24(1,24) = {d}\n", .{shr24(ld(u24, &u24_one), ld(u5, &c24))}),
        12 => p("divExactU(7,3) = {d}\n", .{divExactU(ld(u32, &u_seven), ld(u32, &u_three))}),
        13 => p("divExactI(minInt,-1) = {d}\n", .{divExactI(min, neg1)}),
        14 => p("divExactU(7,0) = {d}\n", .{divExactU(ld(u32, &u_seven), ld(u32, &u_zero))}),
        15 => p("divTruncI(minInt,-1) = {d}\n", .{divTruncI(min, neg1)}),
        16 => p("divFloorI(minInt,-1) = {d}\n", .{divFloorI(min, neg1)}),
        17 => p("divU(7,0) = {d}\n", .{divU(ld(u32, &u_seven), ld(u32, &u_zero))}),
        18 => p("remI(7,0) = {d}\n", .{remI(7, ld(i32, &i_zero))}),
        19 => p("modI(7,0) = {d}\n", .{modI(7, ld(i32, &i_zero))}),
        20 => p("addU(0x80000000,0x80000000) = {d}\n", .{addU(top, top)}),
        21 => p("subU(1,3) = {d}\n", .{subU(ld(u32, &u_one), ld(u32, &u_three))}),
        22 => p("mulI(minInt,-1) = {d}\n", .{mulI(min, neg1)}),
        23 => p("addV = {any}\n", .{addV(.{ top, 1 }, .{ top, 1 })}),
        24 => p("intCastU8(0x80000000) = {d}\n", .{intCastU8(top)}),
        25 => p("intCastNeg(-3) = {d}\n", .{intCastNeg(ld(i32, &i_neg3))}),
        26 => p("intFromFloat(1e10) = {d}\n", .{intFromFloat(ld(f64, &big))}),
        27 => p("enumFromInt(9) = {d}\n", .{@intFromEnum(enumFromInt(ld(u8, &nine)))}),
        28 => p("negI(minInt) = {d}\n", .{negI(min)}),
        else => p("no case {d}\n", .{case}),
    }
}
