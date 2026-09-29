//! atomics's differential-test dispatch (examples/atomics/atomics.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! Each function takes no argument and runs its own threads; each input line is one run with the
//! OS scheduler's own interleaving. The Lean side searches the schedules for the result that
//! real Zig reported (tests/diff/Diff.lean's `searchSchedules`, docs/std-models.md §Thread model).

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep atomics --dep common -Mroot=tests/diff/atomics/harness.zig \
//   -Matomics=examples/atomics/atomics.zig -Mcommon=tests/diff/common.zig
const atomics = @import("atomics");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype) !void {
    try common.forEachLine(gpa, "atomics", name, struct {
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

    try common.makePath("tests/diff/out/zig/atomics");

    try run(gpa, "mpRelAcq", atomics.mpRelAcq);
    try run(gpa, "mpRelaxed", atomics.mpRelaxed);
    try run(gpa, "sbRelaxed", atomics.sbRelaxed);
    try run(gpa, "twoPlusTwoW", atomics.twoPlusTwoW);
    try run(gpa, "stackPush", atomics.stackPush);
}
