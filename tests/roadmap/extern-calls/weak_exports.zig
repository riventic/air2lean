//! Symbols that `@export` defines (docs/air-json.md §Export table), called through `extern`
//! declarations of the same compilation, as a program calls Zig's libc (`lib/c.zig` exports
//! every symbol with weak linkage). The weak definition binds under premise EXT-07 only; the
//! strong one binds like an `export fn`.

fn clampAdd(a: u32, b: u32) callconv(.c) u32 {
    return a +| b;
}

fn twice(a: u32) callconv(.c) u32 {
    return a *% 2;
}

comptime {
    @export(&clampAdd, .{ .name = "weak_clamp_add", .linkage = .weak, .visibility = .hidden });
    @export(&twice, .{ .name = "strong_twice", .linkage = .strong });
}

extern fn weak_clamp_add(a: u32, b: u32) u32;
extern fn strong_twice(a: u32) u32;

export fn viaWeak(a: u32, b: u32) u32 {
    return weak_clamp_add(a, b);
}

export fn viaStrong(a: u32) u32 {
    return strong_twice(a);
}
