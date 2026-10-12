const S = struct { a: u32, b: u32 };
pub fn cast(x: u64) S {
    return @bitCast(x);
}
comptime {
    _ = &cast;
}
