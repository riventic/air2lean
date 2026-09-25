//! Errors: `parseDigit` returns an error union; `sumDigits` propagates it with `try` in a
//! loop; `digitOrZero` discards it with `catch`.

const std = @import("std");

/// ASCII digit to its value, or `error.NotDigit`.
pub fn parseDigit(c: u8) error{NotDigit}!u8 {
    if (c < '0' or c > '9') return error.NotDigit;
    return c - '0';
}

/// Sum of the digit values in `s`. Fails on the first non-digit byte. `total` is u32 and each
/// digit is at most 9, so overflow would need about 4.8e8 bytes — unreachable in tests.
pub fn sumDigits(s: []const u8) error{NotDigit}!u32 {
    var total: u32 = 0;
    for (s) |c| {
        total += try parseDigit(c);
    }
    return total;
}

/// `parseDigit`, defaulting to 0 on error.
export fn digitOrZero(c: u8) u8 {
    return parseDigit(c) catch 0;
}

comptime {
    _ = &parseDigit;
    _ = &sumDigits;
}

test "parseDigit" {
    try std.testing.expectEqual(@as(u8, 0), try parseDigit('0'));
    try std.testing.expectEqual(@as(u8, 9), try parseDigit('9'));
    try std.testing.expectError(error.NotDigit, parseDigit('/'));
    try std.testing.expectError(error.NotDigit, parseDigit(':'));
}

test "sumDigits" {
    try std.testing.expectEqual(@as(u32, 0), try sumDigits(""));
    try std.testing.expectEqual(@as(u32, 45), try sumDigits("0123456789"));
    try std.testing.expectError(error.NotDigit, sumDigits("12a4"));
}

test "digitOrZero" {
    try std.testing.expectEqual(@as(u8, 5), digitOrZero('5'));
    try std.testing.expectEqual(@as(u8, 0), digitOrZero('/'));
    try std.testing.expectEqual(@as(u8, 0), digitOrZero(':'));
}
