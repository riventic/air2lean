//! sync's differential-test dispatch (examples/sync/sync.zig, Zig 0.16.0 only:
//! examples/sync/zig-versions). Shared runner code (fork/panic/render/JSONL plumbing) lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! Each function takes the `std.Io` of an `std.Io.Threaded`; each input line is one run with
//! the OS scheduler's own interleaving. The Lean side searches the schedules for the result
//! that real Zig reported (tests/diff/Diff.lean's `searchSchedules`).

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep sync --dep common -Mroot=tests/diff/sync/harness.zig \
//   -Msync=examples/sync/sync.zig -Mcommon=tests/diff/common.zig
const sync = @import("sync");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

var threaded: std.Io.Threaded = undefined;

fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype) !void {
    try common.forEachLine(gpa, "sync", name, struct {
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

    try common.makePath("tests/diff/out/zig/sync");

    try run(gpa, "mutexCounter", sync.mutexCounter);
    try run(gpa, "handoff", sync.handoff);
    try run(gpa, "semaphoreCounter", sync.semaphoreCounter);
    try run(gpa, "rwLockRead", sync.rwLockRead);
}
