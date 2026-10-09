//! A union whose only inhabited variant is next to a `noreturn` one, in memory. Zig 0.16.0
//! stores no tag for it (one possible active field), so its size is the payload's (2); the model
//! stores the tag and computes 4. The checker rejects the mismatch, also inside a struct whose
//! own size agrees (README.md).
const One = @import("noreturn_variants.zig").One;

const Pair = struct { o: One, n: u32 };

fn readOne(p: *const One) u16 {
    return switch (p.*) {
        .never => unreachable,
        .only => |n| n,
    };
}

pub fn memOne(n: u16) u16 {
    var o: One = .{ .only = n };
    return readOne(&o);
}

fn readPair(p: *const Pair) u32 {
    return p.n;
}

pub fn memPair(n: u32) u32 {
    var pair: Pair = .{ .o = .{ .only = 1 }, .n = n };
    return readPair(&pair);
}

comptime {
    _ = &memOne;
    _ = &memPair;
}
