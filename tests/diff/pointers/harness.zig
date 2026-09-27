//! pointers's differential-test dispatch (examples/pointers/pointers.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! Every function here uses memory: an input line is `{"bufs":[…],"args":[…]}`, a pointer
//! argument is `{"buf":i,"off":o}` into those buffers, and the result line also has the bytes of
//! the buffers after the call (common.forkCallBufs).

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep pointers --dep common -Mroot=tests/diff/pointers/harness.zig \
//   -Mpointers=examples/pointers/pointers.zig -Mcommon=tests/diff/common.zig
const pointers = @import("pointers");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

const Job = pointers.Job;
const ptr = common.ptrArg;

fn int(comptime T: type, v: std.json.Value) T {
    return @intCast(v.integer);
}

/// Runs `func` on each input line of `name`; `args` builds its argument tuple from the line.
fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool, comptime args: anytype) !void {
    try common.forEachMemLine(gpa, "pointers", name, struct {
        fn call(_: std.mem.Allocator, bufs: []common.Buf, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            const outcome = try common.forkCallBufs(Args, args(bufs, items), func, quote_wide, bufs);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argSwap(b: []common.Buf, it: []std.json.Value) struct { *u32, *u32 } {
    return .{ ptr(*u32, b, it[0]), ptr(*u32, b, it[1]) };
}
fn argDelay(b: []common.Buf, it: []std.json.Value) struct { *Job, u32 } {
    return .{ ptr(*Job, b, it[0]), int(u32, it[1]) };
}
fn argMaxPtr(b: []common.Buf, it: []std.json.Value) struct { ?*const u32, ?*const u32 } {
    return .{ ptr(?*const u32, b, it[0]), ptr(?*const u32, b, it[1]) };
}
fn argDueOf(b: []common.Buf, it: []std.json.Value) struct { *Job } {
    return .{ptr(*Job, b, it[0])};
}
fn argSumTo(_: []common.Buf, it: []std.json.Value) struct { u32 } {
    return .{int(u32, it[0])};
}
fn argCopyJob(b: []common.Buf, it: []std.json.Value) struct { *Job, *const Job } {
    return .{ ptr(*Job, b, it[0]), ptr(*const Job, b, it[1]) };
}
fn argBumpOpt(b: []common.Buf, it: []std.json.Value) struct { *?u32 } {
    return .{ptr(*?u32, b, it[0])};
}
fn argSetOpt(b: []common.Buf, it: []std.json.Value) struct { *?u32, ?u32 } {
    return .{ ptr(*?u32, b, it[0]), if (it[1] == .null) null else int(u32, it[1]) };
}
fn argSetOptJob(b: []common.Buf, it: []std.json.Value) struct { *?Job, u32 } {
    return .{ ptr(*?Job, b, it[0]), int(u32, it[1]) };
}
fn argAddDown(b: []common.Buf, it: []std.json.Value) struct { *u64, u32 } {
    return .{ ptr(*u64, b, it[0]), int(u32, it[1]) };
}
fn argSame(b: []common.Buf, it: []std.json.Value) struct { *const u32, *const u32 } {
    return .{ ptr(*const u32, b, it[0]), ptr(*const u32, b, it[1]) };
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/pointers");

    try run(gpa, "swap", pointers.swap, false, argSwap);
    try run(gpa, "delay", pointers.delay, false, argDelay);
    try run(gpa, "maxPtr", pointers.maxPtr, false, argMaxPtr);
    try run(gpa, "dueOf", pointers.dueOf, false, argDueOf);
    try run(gpa, "sumTo", pointers.sumTo, true, argSumTo);
    try run(gpa, "copyJob", pointers.copyJob, false, argCopyJob);
    try run(gpa, "bumpOpt", pointers.bumpOpt, false, argBumpOpt);
    try run(gpa, "setOpt", pointers.setOpt, false, argSetOpt);
    try run(gpa, "same", pointers.same, false, argSame);
    try run(gpa, "setOptJob", pointers.setOptJob, false, argSetOptJob);
    try run(gpa, "addDown", pointers.addDown, false, argAddDown);
}
