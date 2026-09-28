//! layout's differential-test dispatch (examples/layout/layout.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! Every function here uses memory: an input line is `{"bufs":[…],"args":[…]}`, a pointer
//! argument is `{"buf":i,"off":o}` into those buffers (common.forkCallBufs). `ptrFromAddr`'s
//! address argument is a plain usize, quoted (docs/generated-code.md's wide-int convention),
//! since it is not a pointer into any buffer.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep layout --dep common -Mroot=tests/diff/layout/harness.zig \
//   -Mlayout=examples/layout/layout.zig -Mcommon=tests/diff/common.zig
const layout = @import("layout");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

const ptr = common.ptrArg;

/// Runs `func` on each input line of `name`; `args` builds its argument tuple from the line.
fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime args: anytype) !void {
    try common.forEachMemLine(gpa, "layout", name, struct {
        fn call(_: std.mem.Allocator, bufs: []common.Buf, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            const outcome = try common.forkCallBufs(Args, args(bufs, items), func, false, bufs);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argAddrEq(b: []common.Buf, it: []std.json.Value) struct { *const u32, *const u32 } {
    return .{ ptr(*const u32, b, it[0]), ptr(*const u32, b, it[1]) };
}
fn argPtrRoundTrip(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argPtrFromAddr(_: []common.Buf, it: []std.json.Value) struct { usize } {
    return .{std.fmt.parseInt(usize, it[0].string, 10) catch unreachable};
}
fn argAsConst(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argDropConst(b: []common.Buf, it: []std.json.Value) struct { *const u32 } {
    return .{ptr(*const u32, b, it[0])};
}
fn argAsVolatile(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argAlign4(b: []common.Buf, it: []std.json.Value) struct { *align(1) u32 } {
    return .{ptr(*align(1) u32, b, it[0])};
}
fn argParentOfX(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argParentOfY(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/layout");

    try run(gpa, "addrEq", layout.addrEq, argAddrEq);
    try run(gpa, "ptrRoundTrip", layout.ptrRoundTrip, argPtrRoundTrip);
    try run(gpa, "ptrFromAddr", layout.ptrFromAddr, argPtrFromAddr);
    try run(gpa, "asConst", layout.asConst, argAsConst);
    try run(gpa, "dropConst", layout.dropConst, argDropConst);
    try run(gpa, "asVolatile", layout.asVolatile, argAsVolatile);
    try run(gpa, "align4", layout.align4, argAlign4);
    try run(gpa, "parentOfX", layout.parentOfX, argParentOfX);
    try run(gpa, "parentOfY", layout.parentOfY, argParentOfY);
}
