// Generic declarations shared by the programs a.zig, a_reordered.zig and b.zig. Each comptime
// argument kind of the instance key (docs/air-json.md §Instances) appears at least once.
pub const Mode = enum { fast, safe };
pub const Pair = struct { a: u32, b: u32 };
pub const limit: u32 = 9;

/// A type and an integer of that type.
pub fn scale(comptime T: type, comptime k: T, x: T) T {
    return x *% k;
}

/// An enum value.
pub fn tagged(comptime m: Mode, x: u32) u32 {
    return switch (m) {
        .fast => x +% 1,
        .safe => x +% 2,
    };
}

/// A string (a pointer into a constant byte array).
pub fn prefixLen(comptime s: []const u8, x: u32) u32 {
    return x +% @as(u32, s.len);
}

/// A function.
pub fn apply(comptime f: fn (u32) u32, x: u32) u32 {
    return f(x);
}

pub fn inc(x: u32) u32 {
    return x +% 1;
}

pub fn dec(x: u32) u32 {
    return x -% 1;
}

/// A struct value.
pub fn first(comptime p: Pair, x: u32) u32 {
    return x +% p.a;
}

/// A pointer to a declaration.
pub fn bounded(comptime p: *const u32, x: u32) u32 {
    return @min(x, p.*);
}

/// An `anytype` parameter: its type is part of the instance, not a comptime argument.
pub fn widen(x: anytype) u64 {
    return x;
}
