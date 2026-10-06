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

fn sourceSignal() u32 {
    std.posix.raise(std.posix.SIG.FPE) catch @panic("raise failed");
    return 7;
}

fn sourceInterrupt() u32 {
    std.posix.raise(std.posix.SIG.TERM) catch @panic("raise failed");
    return 7;
}

fn rendererSignal() *const u8 {
    // The tested call returns; reading this payload belongs to the renderer phase.
    return @ptrFromInt(1);
}

fn signal(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(std.meta.ArgsTuple(@TypeOf(sourceSignal)), .{}, sourceSignal, false));
}

fn interrupt(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(std.meta.ArgsTuple(@TypeOf(sourceInterrupt)), .{}, sourceInterrupt, false));
}

fn rendererFault(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(std.meta.ArgsTuple(@TypeOf(rendererSignal)), .{}, rendererSignal, false));
}

fn prefix(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(std.meta.ArgsTuple(@TypeOf(value)), .{}, value, false));
}

fn renderer(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    // Only result rendering receives this zero-capacity allocator. The tested
    // function still runs first, returns 7 and takes no allocator argument.
    var bytes: [0]u8 = .{};
    var fixed = std.heap.FixedBufferAllocator.init(&bytes);
    const outcome = try common.forkCallBufsWithRenderingAllocator(
        std.meta.ArgsTuple(@TypeOf(value)), .{}, value, false, null, fixed.allocator(),
    );
    switch (outcome) {
        .fail => |failure| if (failure.kind != .native_harness_failure)
            return error.RendererMisclassified,
        .ok => return error.RendererFailureMissing,
    }
    try common.writeResult(writer, outcome);
}

fn source(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(sourcePanic)), .{}, sourcePanic, false);
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
    try common.forEachLine(allocator, "outcome-accounting", "signal", signal);
    try common.forEachLine(allocator, "outcome-accounting", "interrupt", interrupt);
    try common.forEachLine(allocator, "outcome-accounting", "renderer-fault", rendererFault);
}
