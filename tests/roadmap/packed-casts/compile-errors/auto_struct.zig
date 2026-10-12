const S = struct { a: u32, b: u32 };
pub fn cast(s: S) u64 {
    return @bitCast(s);
}
comptime {
    _ = &cast;
}
