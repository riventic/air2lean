const E = extern struct { a: u32, b: u32 };
pub fn cast(e: E) u64 {
    return @bitCast(e);
}
comptime {
    _ = &cast;
}
