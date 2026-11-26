const std = @import("std");

/// M04: the lower-level entry points of `std.mem.Allocator` as a client calls them: `rawAlloc`,
/// `rawResize`, `rawRemap` and `rawFree` (the vtable calls, with the byte length and the
/// alignment as the client gives them) and the in-place `resize` of a typed slice. The raw calls
/// are at alignment 4.
const al: std.mem.Alignment = .@"4";

fn take(a: std.mem.Allocator, n: usize) ?[*]u8 {
    return a.rawAlloc(n, al, @returnAddress());
}
fn fit(a: std.mem.Allocator, m: []u8, n: usize) bool {
    return a.rawResize(m, al, n, @returnAddress());
}
fn move(a: std.mem.Allocator, m: []u8, n: usize) ?[*]u8 {
    return a.rawRemap(m, al, n, @returnAddress());
}
fn give(a: std.mem.Allocator, m: []u8) void {
    a.rawFree(m, al, @returnAddress());
}
/// The in-place `resize` of a `[]u32` to `n` items.
fn refit(a: std.mem.Allocator, m: []u32, n: usize) bool {
    return a.resize(m, n);
}

comptime {
    _ = &take;
    _ = &fit;
    _ = &move;
    _ = &give;
    _ = &refit;
}
