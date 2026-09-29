//! threads's differential-test dispatch (examples/threads/threads.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! None of these functions take a pointer/allocator arg visible to the harness (each spawns its
//! own threads and local state internally), so this uses the plain `forEachLine`/`forkCall`
//! pair, like tests/diff/options/harness.zig.
//!
//! parallelCounter is race-free (an atomic `fetchAdd`): the Lean and Zig sides must agree on the
//! exact value, `4 * itersPerThread`. race and xchgRace both race two threads on one shared
//! location: race's plain writes are a data race, so the Lean side throws `.illegal` for every
//! input (tests/diff/threads/unspecified.txt); xchgRace's atomic swaps give `a` or `b`, and
//! the Lean side searches the schedules for the one that real Zig reported
//! (tests/diff/Diff.lean's `searchSchedules`, docs/std-models.md §Thread model).

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep threads --dep common -Mroot=tests/diff/threads/harness.zig \
//   -Mthreads=examples/threads/threads.zig -Mcommon=tests/diff/common.zig
const threads = @import("threads");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn int(comptime T: type, v: std.json.Value) T {
    return @intCast(v.integer);
}

fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime args: anytype) !void {
    try common.forEachLine(gpa, "threads", name, struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(func)), args(items), func, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argCounter(it: []std.json.Value) struct { u32 } {
    return .{int(u32, it[0])};
}
fn argRace(it: []std.json.Value) struct { u32, u32 } {
    return .{ int(u32, it[0]), int(u32, it[1]) };
}
fn argNone(_: []std.json.Value) std.meta.ArgsTuple(@TypeOf(threads.claimOnce)) {
    return .{};
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/threads");

    try run(gpa, "parallelCounter", threads.parallelCounter, argCounter);
    try run(gpa, "race", threads.race, argRace);
    try run(gpa, "xchgRace", threads.xchgRace, argRace);
    try run(gpa, "claimOnce", threads.claimOnce, argNone);
}
