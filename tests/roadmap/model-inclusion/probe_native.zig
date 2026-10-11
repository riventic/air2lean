//! W3 native leg for the architecture-audit allocator probes
//! (`tests/roadmap/architecture-audit/models/alloc_probe.zig`) with each REAL std allocator.
//! The FixedBufferAllocator here is over the probe's caller-visible `arena_bytes` (the audit's
//! D-ALLOC-ALIAS setting). Prints `<probe>=<value>` or `<probe>=error.<Name>` to stderr.
//! Usage: probe_native page|fixed_buffer|arena|debug
const std = @import("std");
const probe = @import("alloc_probe");

fn show(name: []const u8, result: anytype) void {
    if (result) |v| {
        std.debug.print("{s}={d}\n", .{ name, v });
    } else |e| {
        std.debug.print("{s}=error.{s}\n", .{ name, @errorName(e) });
    }
}

pub fn main(init: std.process.Init.Minimal) !void {
    if (init.args.vector.len != 2) return error.Usage;
    const kind = std.mem.span(init.args.vector[1]);
    var fba = std.heap.FixedBufferAllocator.init(&probe.arena_bytes);
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    var debug: std.heap.DebugAllocator(.{}) = .init;
    const a: std.mem.Allocator = if (std.mem.eql(u8, kind, "page"))
        std.heap.page_allocator
    else if (std.mem.eql(u8, kind, "fixed_buffer"))
        fba.allocator()
    else if (std.mem.eql(u8, kind, "arena"))
        arena.allocator()
    else if (std.mem.eql(u8, kind, "debug"))
        debug.allocator()
    else
        return error.Usage;
    show("aliasProbe", probe.aliasProbe(a));
    show("remapProbe", probe.remapProbe(a));
}
