//! Recursion: self-recursive gcd, mutually recursive isEven/isOdd, recursive fact.
//! isEven/isOdd/fact each recurse n times; tests/diff/gen_inputs.zig caps n at 1000 so
//! neither the Zig stack nor the Lean runtime overflows.

const std = @import("std");

/// Euclid's algorithm. Self-recursive; depth is O(log(min(a,b))), so any u32 is safe.
export fn gcd(a: u32, b: u32) u32 {
    if (b == 0) return a;
    return gcd(b, a % b);
}

/// Mutually recursive with isOdd. Recurses n times, one decrement per step.
export fn isEven(n: u32) bool {
    if (n == 0) return true;
    return isOdd(n - 1);
}

/// Mutually recursive with isEven. Recurses n times.
export fn isOdd(n: u32) bool {
    if (n == 0) return false;
    return isEven(n - 1);
}

/// Recursive factorial with a checked multiply. 12! fits in u32; 13! overflows and panics.
/// Recurses n times, so callers must bound n (tests/diff inputs keep it <= 1000).
export fn fact(n: u32) u32 {
    if (n == 0) return 1;
    return n * fact(n - 1);
}

test "gcd" {
    try std.testing.expectEqual(@as(u32, 6), gcd(48, 18));
    try std.testing.expectEqual(@as(u32, 1), gcd(17, 5));
    try std.testing.expectEqual(@as(u32, 0), gcd(0, 0));
    try std.testing.expectEqual(@as(u32, 5), gcd(0, 5));
    try std.testing.expectEqual(@as(u32, 5), gcd(5, 0));
}

test "isEven and isOdd" {
    try std.testing.expect(isEven(0));
    try std.testing.expect(!isOdd(0));
    try std.testing.expect(!isEven(1));
    try std.testing.expect(isOdd(1));
    try std.testing.expect(isEven(1000));
    try std.testing.expect(isOdd(999));
}

test "fact" {
    try std.testing.expectEqual(@as(u32, 1), fact(0));
    try std.testing.expectEqual(@as(u32, 1), fact(1));
    try std.testing.expectEqual(@as(u32, 479001600), fact(12));
    // fact(13) overflows the checked multiply and panics — a trap, not a value, so it is not
    // exercised as a unit test. See tests/diff/recursion/inputs/fact.jsonl for that case.
}
