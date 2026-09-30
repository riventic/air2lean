//! iogroup's differential-test dispatch (examples/iogroup/iogroup.zig, Zig 0.16.0 only:
//! examples/iogroup/zig-versions). Shared runner code (fork/panic/render/JSONL plumbing) lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! Each function takes the `std.Io` of an `std.Io.Threaded`; each input line is one run. The
//! Lean side runs each group task as a thread and searches the schedules for the result that
//! real Zig reported (tests/diff/Diff.lean's `searchSchedules`).

const std = @import("std");
const iogroup = @import("iogroup");
const common = @import("common");

pub const panic = common.panic;

var threaded: std.Io.Threaded = undefined;

fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype) !void {
    try common.forEachLine(gpa, "iogroup", name, struct {
        fn call(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(func)), .{threaded.io()}, func, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    threaded = .init(std.heap.page_allocator, .{});
    defer threaded.deinit();

    try common.makePath("tests/diff/out/zig/iogroup");

    try run(gpa, "groupCounter", iogroup.groupCounter);
    try run(gpa, "groupConcurrent", iogroup.groupConcurrent);
}
