//! Small float functions: plain arithmetic (lerp, hypot2), a branch (clamp), a NaN check
//! (isNan), an optional result (celsius), and a slice reduction (dot). Bodies are fixed —
//! Proofs/Floats depends on them exactly; do not reformat.

const std = @import("std");

export fn lerp(a: f64, b: f64, t: f64) f64 { return a + (b - a) * t; }
export fn clamp(x: f32, lo: f32, hi: f32) f32 { return if (x < lo) lo else if (x > hi) hi else x; }
export fn isNan(x: f64) bool { return x != x; }
export fn hypot2(a: f64, b: f64) f64 { return @sqrt(a * a + b * b); }
pub fn celsius(k: f32) ?f32 { return if (k < 0) null else k - 273.15; }
pub fn dot(xs: []const f64, ys: []const f64) f64 { var s: f64 = 0; for (xs, ys) |x, y| s += x * y; return s; }

comptime {
    _ = &celsius;
    _ = &dot;
}

test "lerp" {
    try std.testing.expectEqual(@as(f64, 5.0), lerp(0.0, 10.0, 0.5));
}

test "clamp" {
    try std.testing.expectEqual(@as(f32, 1.0), clamp(0.5, 1.0, 2.0));
    try std.testing.expectEqual(@as(f32, 2.0), clamp(3.0, 1.0, 2.0));
    try std.testing.expectEqual(@as(f32, 1.5), clamp(1.5, 1.0, 2.0));
}

test "isNan" {
    try std.testing.expect(isNan(std.math.nan(f64)));
    try std.testing.expect(!isNan(1.0));
}

test "hypot2" {
    try std.testing.expectEqual(@as(f64, 5.0), hypot2(3.0, 4.0));
}

test "celsius" {
    try std.testing.expectEqual(@as(?f32, null), celsius(-1.0));
    try std.testing.expectEqual(@as(?f32, 0.0), celsius(273.15));
}

test "dot" {
    try std.testing.expectEqual(@as(f64, 0.0), dot(&.{}, &.{}));
    try std.testing.expectEqual(@as(f64, 32.0), dot(&.{ 1.0, 2.0, 3.0 }, &.{ 4.0, 5.0, 6.0 }));
}
