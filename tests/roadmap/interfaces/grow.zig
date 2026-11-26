const std = @import("std");

/// M04: growth of a sentinel slice itself. `realloc`, `remap` and `resize` are called with the
/// `[:0]T`, not with its absorbed `len + 1`-item buffer as in `wide.zig`: std accounts for the
/// sentinel item (`mem.absorbSentinel`, Zig 0.17). Zig 0.16.0 rejects these calls at compile
/// time, so this program is not exported there. The instances are `u8` and `u32`.
fn Buf(comptime T: type) type {
    return struct {
        fn append(a: std.mem.Allocator, s: [:0]T, c: T) ![:0]T {
            const g = try a.realloc(s, s.len + 2);
            g[s.len] = c;
            g[s.len + 1] = 0;
            return g[0 .. s.len + 1 :0];
        }
        fn resize(a: std.mem.Allocator, s: [:0]T, n: usize) ![:0]T {
            const g = try a.realloc(s, n + 1);
            g[n] = 0;
            return g[0..n :0];
        }
        /// `remap` to `n` items and the sentinel: the moved or resized buffer, or `null`.
        fn move(a: std.mem.Allocator, s: [:0]T, n: usize) ?[:0]T {
            const g = a.remap(s, n + 1) orelse return null;
            g[n] = 0;
            return g[0..n :0];
        }
        /// In-place `resize` to `n` items and the sentinel: whether the allocator did it.
        fn fit(a: std.mem.Allocator, s: [:0]T, n: usize) bool {
            if (!a.resize(s, n + 1)) return false;
            s.ptr[n] = 0;
            return true;
        }
    };
}

comptime {
    for (.{ u8, u32 }) |T| {
        _ = &Buf(T).append;
        _ = &Buf(T).resize;
        _ = &Buf(T).move;
        _ = &Buf(T).fit;
    }
}
