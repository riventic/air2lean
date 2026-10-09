//! W3 native leg: the `lists` differential functions with a REAL std allocator instead of the
//! model mirror `common.TestAllocator`. Same inputs (`tests/diff/lists/inputs`, relative to the
//! working directory), same fork/render protocol (`tests/diff/common.zig`), so each output line
//! is comparable with the model's lines; there is no live-allocation count (a real allocator
//! has no model count). The allocation-policy argument of each input is ignored: the real
//! allocator decides. Build with stock Zig (tests/roadmap/model-inclusion/check.sh):
//!   zig build-exe -OReleaseSafe -mcpu=baseline --dep lists --dep common \
//!     -Mroot=tests/roadmap/model-inclusion/lists_native.zig \
//!     -Mlists=examples/lists/lists.zig -Mcommon=tests/diff/common.zig
//! Usage: lists_native page|fixed_buffer|arena|debug
const std = @import("std");
const lists = @import("lists");
const common = @import("common");

pub const panic = common.panic;

const slice = common.sliceArg;

/// The FixedBufferAllocator's memory: private to the harness, so it never aliases an input.
var fba_buffer: [64 << 20]u8 = undefined;
var real: std.mem.Allocator = undefined;

fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool, comptime args: anytype) !void {
    try common.forEachMemLine(gpa, "lists", name, struct {
        fn call(_: std.mem.Allocator, bufs: []common.Buf, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            // Each call runs in a forked child, so every input starts from the same allocator state.
            const outcome = try common.forkCallBufs(Args, .{real} ++ args(bufs, items[1..]), func, quote_wide, bufs);
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

pub fn main(init: std.process.Init.Minimal) !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    if (init.args.vector.len != 2) return error.Usage;
    const kind = std.mem.span(init.args.vector[1]);
    var fba = std.heap.FixedBufferAllocator.init(&fba_buffer);
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    var debug: std.heap.DebugAllocator(.{}) = .init;
    if (std.mem.eql(u8, kind, "page")) {
        real = std.heap.page_allocator;
    } else if (std.mem.eql(u8, kind, "fixed_buffer")) {
        real = fba.allocator();
    } else if (std.mem.eql(u8, kind, "arena")) {
        real = arena.allocator();
    } else if (std.mem.eql(u8, kind, "debug")) {
        real = debug.allocator();
    } else return error.Usage;

    try common.makePath("tests/diff/out/zig/lists");
    try run(gpa, "sumRange", lists.sumRange, true, argUsize);
    try run(gpa, "dupe", lists.dupe, false, argBytes);
    try run(gpa, "dupeZLen", lists.dupeZLen, false, argBytes);
    try run(gpa, "evens", lists.evens, false, argItems);
    try run(gpa, "listSum", lists.listSum, true, argItems);
}
