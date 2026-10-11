//! Architecture audit (models, area 5): allocator-model divergences.
//! Every function takes an arbitrary `std.mem.Allocator`. In the default
//! `--allocator-model std` the translator replaces that type by the single model allocator
//! `Zig.Allocator` (`Air2Lean/Air/Json.lean`, `Ty.allocator`) and its calls by
//! `ZigLean/Mem/Alloc.lean`, whatever allocator the caller actually passes.
const std = @import("std");

/// Caller-visible memory. `native.zig` backs a FixedBufferAllocator with it.
pub var arena_bytes: [16]u8 = [_]u8{0} ** 16;

/// D-ALLOC-ALIAS: the model's `create` returns a fresh block disjoint from every existing
/// block, so `arena_bytes[0]` is unchanged for every allocation policy (result 0 or
/// OutOfMemory). An allocator that hands out caller-visible memory (FixedBufferAllocator over
/// `arena_bytes`, any user allocator over a static buffer) returns 42.
pub fn aliasProbe(a: std.mem.Allocator) !u8 {
    const p = try a.create(u8);
    p.* = 42;
    const seen = arena_bytes[0];
    a.destroy(p);
    return seen;
}

/// D-ALLOC-REMAP: `Zig.Allocator.remap` returns `null` for every nonempty slice whose items
/// are wider than one byte, under every `Mem.allocPolicy`. `std.heap.page_allocator` shrinks
/// a one-page `[]u32` in place and returns the slice (result 1).
pub fn remapProbe(a: std.mem.Allocator) !u32 {
    const s = try a.alloc(u32, 1024);
    if (a.remap(s, 512)) |t| {
        a.free(t);
        return 1;
    }
    a.free(s);
    return 0;
}

comptime {
    _ = &aliasProbe;
    _ = &remapProbe;
}
