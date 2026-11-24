const E = error{ A, B };
pub fn cast(a: [2]E!u16) u64 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
