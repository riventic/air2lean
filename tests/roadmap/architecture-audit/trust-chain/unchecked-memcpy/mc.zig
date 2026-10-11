export fn shiftCopy(buf: [*]u8, n: usize) void {
    @setRuntimeSafety(false);
    @memcpy(buf[1 .. n + 1], buf[0..n]);
}
export fn shiftCopySafe(buf: [*]u8, n: usize) void {
    @memcpy(buf[1 .. n + 1], buf[0..n]);
}
