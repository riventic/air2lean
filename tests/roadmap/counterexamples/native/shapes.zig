//! P08 fixture for goal search over value shapes: per shape one function with a seeded bug and
//! its correct twin (`…Ok`). Each is exported by a patched compiler, translated, searched for a
//! violation of the contract stated at the function and replayed against the native program.

pub const Point = struct { x: u8, y: u8 };
pub const Color = enum(u8) { red, green, blue };
/// Signed, non-contiguous tag values.
pub const Level = enum(i8) { low = -1, mid = 0, high = 5 };
pub const Range = error{ Zero, TooBig };
pub const Shape = union(enum) { circle: u8, rect: Point, empty };
/// Nested: a struct in a struct, an optional field and an enum field.
pub const Span = struct { at: Point, len: ?u8, tint: Color };

/// struct. Contract: the point with its coordinates exchanged.
pub fn mirror(p: Point) Point {
    return .{ .x = p.y, .y = p.y }; // seeded bug: `y` is not `p.x`
}

pub fn mirrorOk(p: Point) Point {
    return .{ .x = p.y, .y = p.x };
}

/// optional result. Contract: `null` for an odd number, else its half.
pub fn half(n: u8) ?u8 {
    if (n % 2 == 1 and n != 1) return null; // seeded bug: 1 is odd
    return n / 2;
}

pub fn halfOk(n: u8) ?u8 {
    if (n % 2 == 1) return null;
    return n / 2;
}

/// optional parameter. Contract: the payload, or 7 for `null`.
pub fn orSeven(o: ?u8) u8 {
    return o orelse 0; // seeded bug: the default
}

pub fn orSevenOk(o: ?u8) u8 {
    return o orelse 7;
}

/// error union. Contract: `Zero` for 0, `TooBig` above 100, else the predecessor.
pub fn pred(n: u8) Range!u8 {
    if (n == 0) return error.Zero;
    if (n > 101) return error.TooBig; // seeded bug: 101 is too big
    return n - 1;
}

pub fn predOk(n: u8) Range!u8 {
    if (n == 0) return error.Zero;
    if (n > 100) return error.TooBig;
    return n - 1;
}

/// enum. Contract: red -> green -> blue -> red.
pub fn next(c: Color) Color {
    return switch (c) {
        .red => .green,
        .green => .blue,
        .blue => .blue, // seeded bug: no wrap
    };
}

pub fn nextOk(c: Color) Color {
    return switch (c) {
        .red => .green,
        .green => .blue,
        .blue => .red,
    };
}

/// enum with signed tag values. Contract: its tag value plus one, as `i16`.
pub fn above(l: Level) i16 {
    return switch (l) {
        .low => 0,
        .mid => 1,
        .high => 5, // seeded bug: 6
    };
}

pub fn aboveOk(l: Level) i16 {
    return @as(i16, @intFromEnum(l)) + 1;
}

/// slice. Contract: the number of items equal to `x`.
pub fn count(xs: []const u8, x: u8) u32 {
    var n: u32 = 0;
    var i: usize = 1; // seeded bug: skips item 0
    while (i < xs.len) : (i += 1) {
        if (xs[i] == x) n += 1;
    }
    return n;
}

pub fn countOk(xs: []const u8, x: u8) u32 {
    var n: u32 = 0;
    for (xs) |item| {
        if (item == x) n += 1;
    }
    return n;
}

/// tagged union. Contract: 3·r for a circle, x+y for a rect, 0 for empty (as `u16`).
pub fn extent(s: Shape) u16 {
    return switch (s) {
        .circle => |r| @as(u16, r) * 3,
        .rect => |p| @as(u16, p.x) + p.x, // seeded bug: `p.y`
        .empty => 0,
    };
}

pub fn extentOk(s: Shape) u16 {
    return switch (s) {
        .circle => |r| @as(u16, r) * 3,
        .rect => |p| @as(u16, p.x) + p.y,
        .empty => 0,
    };
}

/// nested. Contract: `Zero` when `len` is null or 0; else the span moved right by `len`
/// (`TooBig` when `at.x + len` does not fit), with `len` and `tint` unchanged.
pub fn advance(s: Span) Range!Span {
    const n = s.len orelse return error.Zero;
    if (n == 0) return error.Zero;
    if (@as(u16, s.at.x) + n > 255) return error.TooBig;
    return .{ .at = .{ .x = s.at.x + n, .y = s.at.y }, .len = s.len, .tint = .red }; // seeded bug: the tint
}

pub fn advanceOk(s: Span) Range!Span {
    const n = s.len orelse return error.Zero;
    if (n == 0) return error.Zero;
    if (@as(u16, s.at.x) + n > 255) return error.TooBig;
    return .{ .at = .{ .x = s.at.x + n, .y = s.at.y }, .len = s.len, .tint = s.tint };
}

/// Not expressible by the goal search: a slice that the function writes through (memory).
pub fn zero(xs: []u8) void {
    for (xs) |*item| item.* = 0;
}

comptime {
    for (.{
        &mirror, &mirrorOk, &half,   &halfOk,   &orSeven, &orSevenOk, &pred,    &predOk,    &next, &nextOk,
        &above,  &aboveOk,  &count,  &countOk,  &extent,  &extentOk,  &advance, &advanceOk, &zero,
    }) |f| _ = f;
}
