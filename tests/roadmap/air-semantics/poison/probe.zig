export fn cmpFar(p: [*]const u8, q: [*]const u8, n: usize) bool {
    return p + n == q;
}
export fn cmpFarLt(p: [*]const u8, q: [*]const u8, n: usize) bool {
    return @intFromPtr(p + n) < @intFromPtr(q);
}
export fn branchFar(p: [*]const u8, n: usize) u8 {
    const r = p + n;
    if (@intFromPtr(r) == 0) return 1;
    return 2;
}
