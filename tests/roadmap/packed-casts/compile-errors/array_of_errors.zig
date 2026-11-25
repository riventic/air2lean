const E = error{ A, B };
pub fn cast(a: [2]E) u32 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
