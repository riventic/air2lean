const std = @import("std");

/// M04: a `[:0]T` of an item type wider than a byte, kept through a caller-supplied allocator.
/// `n` items and the sentinel are `(n + 1) * @sizeOf(T)` bytes at `@alignOf(T)`. As in
/// `../sentinel-realloc/source.zig` (the `u8` instance), `append` and `resize` reallocate the
/// absorbed `len + 1`-item buffer (Zig 0.16.0 rejects `realloc` of a sentinel slice) and store
/// the sentinel at the new length. The instances are `u16`, `u32` and `u64`.
fn Buf(comptime T: type) type {
    return struct {
        fn make(a: std.mem.Allocator, n: usize) ![:0]T {
            return a.allocSentinel(T, n, 0);
        }
        fn append(a: std.mem.Allocator, s: [:0]T, c: T) ![:0]T {
            const g = try a.realloc(s.ptr[0 .. s.len + 1], s.len + 2);
            g[s.len] = c;
            g[s.len + 1] = 0;
            return g[0 .. s.len + 1 :0];
        }
        fn resize(a: std.mem.Allocator, s: [:0]T, n: usize) ![:0]T {
            const g = try a.realloc(s.ptr[0 .. s.len + 1], n + 1);
            g[n] = 0;
            return g[0..n :0];
        }
        fn release(a: std.mem.Allocator, s: [:0]T) void {
            a.free(s);
        }
    };
}

comptime {
    for (.{ u16, u32, u64 }) |T| {
        _ = &Buf(T).make;
        _ = &Buf(T).append;
        _ = &Buf(T).resize;
        _ = &Buf(T).release;
    }
}
