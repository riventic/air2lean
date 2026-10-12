//! L07: Zig 0.14.1 and 0.15.2 check only the outer types of a `@bitCast`, so an array of `auto`
//! structs or tagged unions is a memory reinterpretation with the compiler's layout (padding and
//! tag bytes included). Zig 0.16.0 and 0.17.0 reject these casts (`compile-errors/`).
pub const S = struct { a: u16, b: u16 };
pub const T = union(enum) { a: u16, b: u8 };

pub fn structsToInt(a: [2]S) u64 {
    return @bitCast(a);
}

/// Field `b` of item 1 of the structs made from `x`.
pub fn structB1(x: u64) u16 {
    const a: [2]S = @bitCast(x);
    return a[1].b;
}

/// The payload of item 1 of the tagged unions made from `x`.
pub fn unionPayload1(x: u64) u16 {
    const t: [2]T = @bitCast(x);
    return switch (t[1]) {
        .a => |v| v,
        .b => |v| v,
    };
}

/// Tagged unions to an integer: their padding bytes are undefined.
pub fn unionsToInt(a: [2]T) u64 {
    return @bitCast(a);
}

comptime {
    _ = &structsToInt;
    _ = &structB1;
    _ = &unionPayload1;
    _ = &unionsToInt;
}
