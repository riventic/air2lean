pub fn t(x: u32) u32 {
    if (x == 0) @trap();
    return x;
}
comptime { _ = &t; }
