//! threadsync's differential-test dispatch (examples/threadsync/threadsync.zig, Zig 0.15.2 only:
//! examples/threadsync/zig-versions). Shared runner code (fork/panic/render/JSONL plumbing) lives
//! in tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! The functions take no arguments; each input line is one run with the OS scheduler's own
//! interleaving. The Lean side searches the schedules for the result that real Zig reported
//! (tests/diff/Diff.lean's `searchSchedules`). On macOS the compiled `Thread.Mutex` is
//! `os_unfair_lock`, on Linux a futex: each host tests its own translation
//! (tests/golden/0.15.2/threadsync/Gen-darwin.lean, Proofs/Threadsync/Gen.lean).

const std = @import("std");
const threadsync = @import("threadsync");
const common = @import("common");

pub const panic = common.panic;

fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype) !void {
    try common.forEachLine(gpa, "threadsync", name, struct {
        fn call(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(func)), .{}, func, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/threadsync");

    try run(gpa, "mutexCounter", threadsync.mutexCounter);
    try run(gpa, "handoff", threadsync.handoff);
    try run(gpa, "waitGroup", threadsync.waitGroup);
}
