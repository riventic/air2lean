//! Deterministic native producer regressions. Run only through the bounded queue.
const std = @import("std");
const common = @import("common");
pub const panic = common.panic;

fn value() u32 {
    return 7;
}

fn sourcePanic() u32 {
    @panic("tested source panic");
}

fn prefix(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(struct {}, .{}, value, false));
}

fn renderer(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    // Only result rendering receives this zero-capacity allocator. The tested
    // function still runs first, returns 7 and takes no allocator argument.
    var bytes: [0]u8 = .{};
    var fixed = std.heap.FixedBufferAllocator.init(&bytes);
    const outcome = try common.forkCallBufsWithRenderingAllocator(
        struct {}, .{}, value, false, null, fixed.allocator(),
    );
    switch (outcome) {
        .fail => |failure| if (failure.kind != .native_harness_failure)
            return error.RendererMisclassified,
        .ok => return error.RendererFailureMissing,
    }
    try common.writeResult(writer, outcome);
}

fn source(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    const outcome = try common.forkCall(struct {}, .{}, sourcePanic, false);
    switch (outcome) {
        .fail => |failure| if (failure.kind != .native_panic)
            return error.SourcePanicMisclassified,
        .ok => return error.SourcePanicMissing,
    }
    try common.writeResult(writer, outcome);
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    try common.makePath("tests/diff/out/zig/outcome-accounting");
    var input_failed = false;
    common.forEachLine(allocator, "outcome-accounting", "prefix", prefix) catch {
        input_failed = true;
    };
    if (!input_failed) return error.MalformedInputAccepted;
    try common.forEachLine(allocator, "outcome-accounting", "renderer", renderer);
    try common.forEachLine(allocator, "outcome-accounting", "source", source);
}
