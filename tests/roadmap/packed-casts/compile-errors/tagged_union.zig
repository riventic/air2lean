const T = union(enum) { a: u32, b: f32 };
pub fn cast(t: T) u64 {
    return @bitCast(t);
}
comptime {
    _ = &cast;
}
