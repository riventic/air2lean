const std = @import("std");
const builtin = @import("builtin");

/// M04: sentinel buffers of other item kinds than an unsigned integer with sentinel `0`, kept
/// through a caller-supplied allocator: a non-zero sentinel (`[:0xff]u8`), an optional pointer
/// item (`[:null]?*u8`), a float item (`[:0]f32`) and an over-aligned slice
/// (`[:0]align(16) u16`, through `allocWithOptions`). As in `wide.zig`, `append` and `resize`
/// reallocate the absorbed `len + 1`-item buffer and store the sentinel at the new length.
/// `A` is the slice's alignment in bytes: `@alignOf(T)`, or more.
fn Buf(comptime T: type, comptime A: comptime_int, comptime z: T) type {
    return struct {
        const S = [:z]align(A) T;
        fn make(a: std.mem.Allocator, n: usize) !S {
            if (A == @alignOf(T)) return a.allocSentinel(T, n, z);
            // `allocWithOptions` takes a `?mem.Alignment` since Zig 0.15, a `?u29` before.
            if (comptime builtin.zig_version.minor >= 15)
                return a.allocWithOptions(T, n, comptime std.mem.Alignment.fromByteUnits(A), z);
            return a.allocWithOptions(T, n, A, z);
        }
        fn append(a: std.mem.Allocator, s: S, c: T) !S {
            const g = try a.realloc(s.ptr[0 .. s.len + 1], s.len + 2);
            g[s.len] = c;
            g[s.len + 1] = z;
            return g[0 .. s.len + 1 :z];
        }
        fn resize(a: std.mem.Allocator, s: S, n: usize) !S {
            const g = try a.realloc(s.ptr[0 .. s.len + 1], n + 1);
            g[n] = z;
            return g[0..n :z];
        }
        fn release(a: std.mem.Allocator, s: S) void {
            a.free(s);
        }
    };
}

const Ff = Buf(u8, 1, 0xff);
const Opt = Buf(?*u8, @alignOf(?*u8), null);
const Flt = Buf(f32, @alignOf(f32), 0);
const Over = Buf(u16, 16, 0);

/// A sentinel copy of a slice: `dupeSentinel` (Zig 0.17), `dupeZ` before.
fn copy(a: std.mem.Allocator, s: []const u8) ![:0]u8 {
    if (comptime @hasDecl(std.mem.Allocator, "dupeSentinel")) return a.dupeSentinel(u8, s, 0);
    return a.dupeZ(u8, s);
}

comptime {
    for (.{ Ff, Opt, Flt, Over }) |B| {
        _ = &B.make;
        _ = &B.append;
        _ = &B.resize;
        _ = &B.release;
    }
    _ = &copy;
}
