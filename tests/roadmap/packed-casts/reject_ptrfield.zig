//! L08, rejected: a pointer field in a packed struct (Zig 0.14.1 and 0.15.2; Zig 0.16 made it a
//! compile error, "pointers cannot be directly bitpacked"). The model's pointers carry provenance,
//! not bits, so the struct has no bit representation (`packedBits`). Each function is translated
//! alone and must be rejected with its diagnostic (`check.sh`, `reject/expected.txt`).
pub const P = packed struct(u128) { tag: u64, ptr: *u32 };

pub fn readThrough(p: P) u32 {
    return p.ptr.*;
}

pub fn make(x: *u32) u64 {
    const p: P = .{ .tag = 5, .ptr = x };
    return p.tag;
}

comptime {
    _ = &readThrough;
    _ = &make;
}
