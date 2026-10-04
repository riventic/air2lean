//! lists's differential-test dispatch (examples/lists/lists.zig). Shared runner code lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! Every function takes a `std.mem.Allocator` and uses the memory protocol
//! (`{"bufs":[…],"args":[…]}`). Its first argument in `args` is the allocation that fails:
//! `null` or its number (common.TestAllocator). A result slice on the heap is
//! `{"bytes":"<hex>"}`, and each line ends with the number of live allocations after the call.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep lists --dep common -Mroot=tests/diff/lists/harness.zig \
//   -Mlists=examples/lists/lists.zig -Mcommon=tests/diff/common.zig
const lists = @import("lists");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

const slice = common.sliceArg;

var test_alloc: common.TestAllocator = undefined;

/// Runs `func` on each input line of `name`; `args` builds its argument tuple, after the
/// allocator, from the line.
fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool, comptime args: anytype) !void {
    try common.forEachMemLine(gpa, "lists", name, struct {
        fn call(policy_gpa: std.mem.Allocator, bufs: []common.Buf, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            test_alloc = try common.TestAllocator.fromJson(policy_gpa, items[0]);
            defer if (test_alloc.failures.len != 0) policy_gpa.free(test_alloc.failures);
            common.test_alloc = &test_alloc;
            defer common.test_alloc = null;
            const a = test_alloc.allocator();
            const outcome = try common.forkCallBufs(Args, .{a} ++ args(bufs, items[1..]), func, quote_wide, bufs);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argUsize(_: []common.Buf, it: []std.json.Value) struct { usize } {
    return .{@intCast(it[0].integer)};
}
fn argBytes(b: []common.Buf, it: []std.json.Value) struct { []const u8 } {
    return .{slice([]const u8, b, it[0])};
}
fn argItems(b: []common.Buf, it: []std.json.Value) struct { []const u32 } {
    return .{slice([]const u32, b, it[0])};
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/lists");

    try run(gpa, "sumRange", lists.sumRange, true, argUsize);
    try run(gpa, "dupe", lists.dupe, false, argBytes);
    try run(gpa, "dupeZLen", lists.dupeZLen, false, argBytes);
    try run(gpa, "evens", lists.evens, false, argItems);
    try run(gpa, "listSum", lists.listSum, true, argItems);
}
