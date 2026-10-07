const std = @import("std");

/// Zig 0.16.0 rejects `realloc` of a `[:0]u8` at compile time. These clients reallocate the
/// absorbed `len + 1`-byte buffer (sentinel byte counted) and store the sentinel at the new end.
pub fn make(a: std.mem.Allocator, n: usize) ![:0]u8 {
    return a.allocSentinel(u8, n, 0);
}
pub fn append(a: std.mem.Allocator, s: [:0]u8, c: u8) ![:0]u8 {
    const g = try a.realloc(s.ptr[0 .. s.len + 1], s.len + 2);
    g[s.len] = c;
    g[s.len + 1] = 0;
    return g[0 .. s.len + 1 :0];
}
pub fn resize(a: std.mem.Allocator, s: [:0]u8, n: usize) ![:0]u8 {
    const g = try a.realloc(s.ptr[0 .. s.len + 1], n + 1);
    g[n] = 0;
    return g[0..n :0];
}
pub fn release(a: std.mem.Allocator, s: [:0]u8) void {
    a.free(s);
}
comptime {
    _ = &make;
    _ = &append;
    _ = &resize;
    _ = &release;
}
