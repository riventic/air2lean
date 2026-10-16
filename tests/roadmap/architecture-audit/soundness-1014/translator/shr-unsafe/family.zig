//! S3b sibling audit (docs/architecture-audit/soundness-2026-10-14.md, §S3): the integer safety
//! checks with runtime safety on, each fed an input that violates it. `CASE=<n> ./family` runs
//! case n; it prints the result when the check did not fire. Inputs come from volatile globals,
//! so nothing folds at compile time.
//!   zig build-exe -OReleaseSafe -lc family.zig        (aarch64-macos: 0.16.0, 0.17.0)
//!   zig build-exe -OReleaseSafe -lc -target aarch64-linux-musl family.zig   (0.14.1, 0.15.2)
//! In ReleaseSafe only the `@shrExact` exactness cases (1, 2, 3, 5) return a value; every other
//! case panics, in 0.14.1 to 0.17.0.
const std = @import("std");

extern "c" fn getenv(name: [*:0]const u8) ?[*:0]const u8;

var g_u32: [4]u32 = .{ 3, 1, 0x80000000, 7 };
var g_i32: [4]i32 = .{ -3, 1, std.math.minInt(i32), -1 };
var g_u24: [2]u24 = .{ 1, 0 };
var g_u5: [2]u5 = .{ 24, 1 };
var g_f64: [1]f64 = .{1e10};
var g_u8: [1]u8 = .{9};

fn vu32(i: usize) u32 {
    return @as(*volatile u32, &g_u32[i]).*;
}
fn vi32(i: usize) i32 {
    return @as(*volatile i32, &g_i32[i]).*;
}
fn vu24(i: usize) u24 {
    return @as(*volatile u24, &g_u24[i]).*;
}
fn vu5(i: usize) u5 {
    return @as(*volatile u5, &g_u5[i]).*;
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
noinline fn shrExact24Count(a: u24, b: u5) u24 {
    return @shrExact(a, b);
}
noinline fn shrExact24Lost(a: u24, b: u5) u24 {
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
noinline fn shlExact24Count(a: u24, b: u5) u24 {
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
    var case: u32 = 0;
    var i: usize = 0;
    while (s[i] != 0) : (i += 1) case = case * 10 + (s[i] - '0');
    const p = std.debug.print;
    switch (case) {
        1 => p("1 shrExactU(3,1) = {d}\n", .{shrExactU(vu32(0), vu5(1))}),
        2 => p("2 shrExactI(-3,1) = {d}\n", .{shrExactI(vi32(0), vu5(1))}),
        3 => p("3 shrExactV({{3,4}},1) = {any}\n", .{shrExactV(.{ vu32(0), 4 }, .{ vu5(1), vu5(1) })}),
        4 => p("4 shrExact24Count(0,24) = {d}\n", .{shrExact24Count(0, vu5(0))}),
        5 => p("5 shrExact24Lost(1,1) = {d}\n", .{shrExact24Lost(vu24(0), vu5(1))}),
        6 => p("6 shlExactU(0x80000000,1) = {d}\n", .{shlExactU(vu32(2), vu5(1))}),
        7 => p("7 shlExactI(minInt,1) = {d}\n", .{shlExactI(vi32(2), vu5(1))}),
        8 => p("8 shlExactV({{0x80000000,1}},1) = {any}\n", .{shlExactV(.{ vu32(2), 1 }, .{ vu5(1), vu5(1) })}),
        9 => p("9 shlExact24Count(0,24) = {d}\n", .{shlExact24Count(0, vu5(0))}),
        10 => p("10 shl24(1,24) = {d}\n", .{shl24(vu24(0), vu5(0))}),
        11 => p("11 shr24(1,24) = {d}\n", .{shr24(vu24(0), vu5(0))}),
        12 => p("12 divExactU(7,3) = {d}\n", .{divExactU(vu32(3), vu32(0))}),
        13 => p("13 divExactI(minInt,-1) = {d}\n", .{divExactI(vi32(2), vi32(3))}),
        14 => p("14 divExactU(7,0) = {d}\n", .{divExactU(vu32(3), @as(u32, @intCast(vu24(1))))}),
        15 => p("15 divTruncI(minInt,-1) = {d}\n", .{divTruncI(vi32(2), vi32(3))}),
        16 => p("16 divFloorI(minInt,-1) = {d}\n", .{divFloorI(vi32(2), vi32(3))}),
        17 => p("17 divU(7,0) = {d}\n", .{divU(vu32(3), @as(u32, @intCast(vu24(1))))}),
        18 => p("18 remI(7,0) = {d}\n", .{remI(7, @as(i32, @intCast(vu24(1))))}),
        19 => p("19 modI(7,0) = {d}\n", .{modI(7, @as(i32, @intCast(vu24(1))))}),
        20 => p("20 addU(0x80000000,0x80000000) = {d}\n", .{addU(vu32(2), vu32(2))}),
        21 => p("21 subU(1,3) = {d}\n", .{subU(vu32(1), vu32(0))}),
        22 => p("22 mulI(minInt,-1) = {d}\n", .{mulI(vi32(2), vi32(3))}),
        23 => p("23 addV = {any}\n", .{addV(.{ vu32(2), 1 }, .{ vu32(2), 1 })}),
        24 => p("24 intCastU8(0x80000000) = {d}\n", .{intCastU8(vu32(2))}),
        25 => p("25 intCastNeg(-3) = {d}\n", .{intCastNeg(vi32(0))}),
        26 => p("26 intFromFloat(1e10) = {d}\n", .{intFromFloat(@as(*volatile f64, &g_f64[0]).*)}),
        27 => p("27 enumFromInt(9) = {d}\n", .{@intFromEnum(enumFromInt(@as(*volatile u8, &g_u8[0]).*))}),
        28 => p("28 negI(minInt) = {d}\n", .{negI(vi32(2))}),
        else => p("no case {d}\n", .{case}),
    }
}
