//! options's differential-test dispatch (examples/options/options.zig: find, findOr,
//! firstIndexPlusOne). Shared runner code (fork/panic/render/JSONL plumbing) lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! find returns `?usize`: common.forkCall/renderPayload write `{"ok":null}` or the quoted
//! decimal value (docs/generated-code.md's optional-result rule). firstIndexPlusOne panics
//! (`unwrapNull`) when `x` is absent — that's the ordinary panic path, no special code needed
//! here.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep options --dep common -Mroot=tests/diff/options/harness.zig \
//   -Moptions=examples/options/options.zig -Mcommon=tests/diff/common.zig
const options = @import("options");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn xsFromJson(a: std.mem.Allocator, items: []std.json.Value) ![]u32 {
    const xs_json = items[0].array.items;
    const xs = try a.alloc(u32, xs_json.len);
    for (xs_json, 0..) |v, i| xs[i] = @intCast(v.integer);
    return xs;
}

fn runFind(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "options", "find", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const xs = try xsFromJson(a, items);
            defer a.free(xs);
            const x: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(options.find)), .{ xs, x }, options.find, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runFindOr(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "options", "findOr", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const xs = try xsFromJson(a, items);
            defer a.free(xs);
            const x: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(options.findOr)), .{ xs, x }, options.findOr, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runFirstIndexPlusOne(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "options", "firstIndexPlusOne", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const xs = try xsFromJson(a, items);
            defer a.free(xs);
            const x: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(options.firstIndexPlusOne)), .{ xs, x }, options.firstIndexPlusOne, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/options");

    try runFind(gpa);
    try runFindOr(gpa);
    try runFirstIndexPlusOne(gpa);
}
