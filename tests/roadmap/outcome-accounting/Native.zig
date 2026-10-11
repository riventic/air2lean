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

fn sourceAbort() u32 {
    std.posix.raise(std.posix.SIG.ABRT) catch @panic("raise failed");
    return 7;
}

fn sourceHang() u32 {
    // Never returns; only the parent's per-case deadline ends it.
    while (true) std.atomic.spinLoopHint();
}

/// 1 when the child runs with core dumps off: RLIMIT_CORE 0 and, on Linux, not dumpable (a
/// piped `core_pattern` handler such as systemd-coredump/apport otherwise runs per crash even
/// with RLIMIT_CORE 0, and a ReleaseFast run with hundreds of crashing inputs stalls a runner).
fn sourceContained() u32 {
    const lim = std.posix.getrlimit(.CORE) catch return 0;
    if (lim.cur != 0) return 0;
    if (@import("builtin").os.tag == .linux and std.os.linux.prctl(@intFromEnum(std.os.linux.PR.GET_DUMPABLE), 0, 0, 0, 0) != 0) return 0;
    return 1;
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

fn abortSignal(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(std.meta.ArgsTuple(@TypeOf(sourceAbort)), .{}, sourceAbort, false));
}

fn hang(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(sourceHang)), .{}, sourceHang, false);
    switch (outcome) {
        .fail => |failure| if (failure.kind != .native_harness_failure)
            return error.HangMisclassified,
        .ok => return error.HangMissing,
    }
    try common.writeResult(writer, outcome);
}

fn contained(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
    try common.writeResult(writer, try common.forkCall(std.meta.ArgsTuple(@TypeOf(sourceContained)), .{}, sourceContained, false));
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
    try common.forEachLine(allocator, "outcome-accounting", "abort", abortSignal);
    try common.forEachLine(allocator, "outcome-accounting", "renderer-fault", rendererFault);
    try common.forEachLine(allocator, "outcome-accounting", "contained", contained);
    common.case_timeout_ns = 300 * std.time.ns_per_ms;
    try common.forEachLine(allocator, "outcome-accounting", "hang", hang);
}
