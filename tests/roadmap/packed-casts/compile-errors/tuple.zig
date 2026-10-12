pub fn cast(t: struct { u32, u32 }) u64 {
    return @bitCast(t);
}
comptime {
    _ = &cast;
}
