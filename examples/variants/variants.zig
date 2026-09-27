pub const Light = enum(u8) { red, yellow, green };

/// Explicit, non-contiguous tag values of a signed tag type.
pub const Prio = enum(i8) { low = -1, mid = 0, high = 5 };

/// Non-exhaustive: every `u8` is a value, only two have names.
pub const Code = enum(u8) { ok = 0, warn = 1, _ };

pub const Rect = struct { w: u32, h: u32 };

pub const Shape = union(enum) {
    circle: u32,
    rect: Rect,
    square: u32,
    empty,
};

pub fn next(l: Light) Light {
    return switch (l) {
        .red => .green,
        .green => .yellow,
        .yellow => .red,
    };
}

/// The light after `n` steps.
pub fn advance(l: Light, n: u32) Light {
    var cur = l;
    var i: u32 = 0;
    while (i < n) : (i += 1) cur = next(cur);
    return cur;
}

/// Panics (`invalidEnumValue`) for `x > 2`.
pub fn lightOf(x: u8) Light {
    return @enumFromInt(x);
}

pub fn prioValue(p: Prio) i8 {
    return @intFromEnum(p);
}

pub fn isUrgent(p: Prio) bool {
    return p == .high;
}

pub fn severity(c: Code) u8 {
    return switch (c) {
        .ok => 0,
        .warn => 1,
        _ => 2,
    };
}

pub fn codeOf(x: u8) Code {
    return @enumFromInt(x);
}

pub fn area(s: Shape) u64 {
    return switch (s) {
        .circle => |r| 3 * @as(u64, r) * r,
        .rect => |rc| @as(u64, rc.w) * rc.h,
        .square => |a| @as(u64, a) * a,
        .empty => 0,
    };
}

pub fn totalArea(shapes: []const Shape) u64 {
    var total: u64 = 0;
    for (shapes) |s| total += area(s);
    return total;
}

/// Panics (`integerOverflow`) if a scaled size does not fit in `u32`.
pub fn scale(s: Shape, k: u32) Shape {
    return switch (s) {
        .circle => |r| .{ .circle = r * k },
        .rect => |rc| .{ .rect = .{ .w = rc.w * k, .h = rc.h * k } },
        .square => |a| .{ .square = a * k },
        .empty => .empty,
    };
}

/// Panics (`inactiveUnionField`) if `s` is not a circle.
pub fn radius(s: Shape) u32 {
    return s.circle;
}

pub fn isRound(s: Shape) bool {
    return s == .circle;
}

comptime {
    _ = &next;
    _ = &advance;
    _ = &lightOf;
    _ = &prioValue;
    _ = &isUrgent;
    _ = &severity;
    _ = &codeOf;
    _ = &area;
    _ = &totalArea;
    _ = &scale;
    _ = &radius;
    _ = &isRound;
}
