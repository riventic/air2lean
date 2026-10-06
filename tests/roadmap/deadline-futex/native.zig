//! Finite API smoke observations; no wake race or wall-clock timing assertion.
const std = @import("std");
const probe = @import("probe");

pub fn main() !void {
    var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
    defer threaded.deinit();
    const io = threaded.io();
    const word: u32 = 0;
    try probe.waitZero(io, &word, 1); // predicate mismatch
    try probe.waitZero(io, &word, 0); // expired duration, same normal-return shape
    const before = probe.observe(io);
    const after = probe.observe(io);
    std.debug.assert(before <= after);
    std.debug.assert(try probe.boundaryClient(io) == 73);
}
