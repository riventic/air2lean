//! M16b: slices, many-pointers, arrays in memory, memory ops, globals and string literals.

/// Reverse the items in place.
pub fn reverse(s: []u32) void {
    if (s.len == 0) return;
    var i: usize = 0;
    var j: usize = s.len - 1;
    while (i < j) : ({
        i += 1;
        j -= 1;
    }) {
        const t = s[i];
        s[i] = s[j];
        s[j] = t;
    }
}

/// Set every item to `v` (`@memset`).
pub fn fill(s: []u8, v: u8) void {
    @memset(s, v);
}

/// Make every item undefined.
pub fn clear(s: []u16) void {
    @memset(s, undefined);
}

/// Copy `len` items from `src` to `dst` in the same slice; the ranges can overlap (`@memmove`).
pub fn copyWithin(s: []u32, dst: usize, src: usize, len: usize) void {
    @memmove(s[dst..][0..len], s[src..][0..len]);
}

/// Copy between two slices of the same length (`@memcpy`: an overlap panics).
pub fn copy(dst: []u8, src: []const u8) void {
    @memcpy(dst, src);
}

const greeting = "hello, world";

/// The index of the first `c` in a string literal.
pub fn indexOfScalar(c: u8) ?usize {
    for (greeting, 0..) |x, i| {
        if (x == c) return i;
    }
    return null;
}

const table = [_]u16{ 1, 1, 2, 6, 24, 120, 720, 5040 };

/// A constant table: `n!` for `n < 8`.
pub fn factorial(n: usize) u16 {
    return table[n];
}

var counter: u32 = 0;

/// A global `var`: add 1, return the new value.
pub fn bump() u32 {
    counter += 1;
    return counter;
}

/// The sum of the bytes before the 0 sentinel.
pub fn sumZ(p: [*:0]const u8) u32 {
    var sum: u32 = 0;
    var i: usize = 0;
    while (p[i] != 0) : (i += 1) sum += p[i];
    return sum;
}

/// The items from `a` to `b`, which must end at a 0 sentinel.
pub fn subZ(s: []const u8, a: usize, b: usize) [:0]const u8 {
    return s[a..b :0];
}

fn sumSlice(s: []const u32) u32 {
    var t: u32 = 0;
    for (s) |x| t += x;
    return t;
}

/// The sum of all items but the first and the last, by the pure `sumSlice`.
pub fn sumMid(s: []u32) u32 {
    return sumSlice(s[1 .. s.len - 1]);
}

/// The sum of the items of an array, by the pure `sumSlice`.
pub fn total(a: *const [3]u32) u32 {
    return sumSlice(a);
}

/// Item `i` of a many-pointer.
pub fn at(p: [*]const u32, i: usize) u32 {
    return p[i];
}

/// Pointer arithmetic: `p + 1`.
pub fn second(p: [*]const u32) u32 {
    return (p + 1)[0];
}

/// Pointer arithmetic: `p + 2 - 1`.
pub fn prevItem(p: [*]const u32) u32 {
    const q = p + 2;
    return (q - 1)[0];
}

pub const Color = enum { red, green, blue };

/// The name of a tag (`@tagName`).
pub fn colorName(c: Color) []const u8 {
    return @tagName(c);
}

/// The name of an error (`@errorName`).
pub fn failName(n: u8) []const u8 {
    const e: error{ Empty, TooLong } = if (n == 0) error.Empty else error.TooLong;
    return @errorName(e);
}

/// An array through a pointer.
pub fn bumpAt(a: *[4]u8, i: usize) u8 {
    a[i] +%= 1;
    return a[3];
}

/// A local array with an item at a runtime index.
pub fn localArr(i: usize) u8 {
    var a = [_]u8{ 1, 2, 3, 4 };
    a[i % 4] += 1;
    return a[0] + a[3];
}

/// The length of an optional slice, 0 for null.
pub fn lenOr(s: ?[]const u8) usize {
    return if (s) |x| x.len else 0;
}

comptime {
    _ = &reverse;
    _ = &fill;
    _ = &clear;
    _ = &copyWithin;
    _ = &copy;
    _ = &indexOfScalar;
    _ = &factorial;
    _ = &bump;
    _ = &sumZ;
    _ = &subZ;
    _ = &sumMid;
    _ = &total;
    _ = &at;
    _ = &second;
    _ = &prevItem;
    _ = &colorName;
    _ = &failName;
    _ = &bumpAt;
    _ = &localArr;
    _ = &lenOr;
}
