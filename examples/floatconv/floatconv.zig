//! Float conversions: int<->float and bit reinterpretation. docs/floats.md documents each
//! op's semantics (`@intFromFloat` truncates and panics out of range on 0.15.2's safety
//! check; `@floatFromInt` rounds; `@floatCast` rounds or is exact; `@bitCast` is the bits).

const std = @import("std");

pub fn toI32(x: f64) i32 {
    return @intFromFloat(x);
}
pub fn toU64(x: f32) u64 {
    return @intFromFloat(x);
}
pub fn toByte(x: f32) u8 {
    return @intFromFloat(x);
}
pub fn fromI64(x: i64) f32 {
    return @floatFromInt(x);
}
pub fn fromU128(x: u128) f64 {
    return @floatFromInt(x);
}
pub fn f64ToF16(x: f64) f16 {
    return @floatCast(x);
}
pub fn f16ToF128(x: f16) f128 {
    return @floatCast(x);
}
pub fn f80ToF64(x: f80) f64 {
    return @floatCast(x);
}
pub fn bits32(x: f32) u32 {
    return @bitCast(x);
}
pub fn ofBits64(x: u64) f64 {
    return @bitCast(x);
}

comptime {
    _ = &toI32;
    _ = &toU64;
    _ = &toByte;
    _ = &fromI64;
    _ = &fromU128;
    _ = &f64ToF16;
    _ = &f16ToF128;
    _ = &f80ToF64;
    _ = &bits32;
    _ = &ofBits64;
}

test "toI32/fromI64" {
    try std.testing.expectEqual(@as(i32, 3), toI32(3.9));
    try std.testing.expectEqual(@as(i32, -3), toI32(-3.9));
    try std.testing.expectEqual(@as(f32, 42.0), fromI64(42));
}

test "toByte/toU64" {
    try std.testing.expectEqual(@as(u8, 255), toByte(255.0));
    try std.testing.expectEqual(@as(u64, 10), toU64(10.9));
}

test "fromU128" {
    try std.testing.expectEqual(@as(f64, 1.0), fromU128(1));
}

test "casts" {
    try std.testing.expectEqual(@as(f128, 1.5), f16ToF128(1.5));
    try std.testing.expectEqual(@as(f64, 1.5), f80ToF64(1.5));
    try std.testing.expectEqual(@as(f16, 1.5), f64ToF16(1.5));
}

test "bits" {
    try std.testing.expectEqual(@as(u32, 0x3f800000), bits32(1.0));
    try std.testing.expectEqual(@as(f64, 1.0), ofBits64(0x3ff0000000000000));
}
