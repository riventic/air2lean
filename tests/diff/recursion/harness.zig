//! recursion's differential-test dispatch (examples/recursion/recursion.zig: gcd, isEven, isOdd,
//! fact). Shared runner code (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig;
//! see its doc comment for the build command and protocol. isEven/isOdd/fact recurse up to
//! max_recursion_n (tests/diff/gen_inputs.zig) call-deep within one forked child — plain native
//! recursion, not extra forking, so that depth is unremarkable.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep recursion --dep common -Mroot=tests/diff/recursion/harness.zig \
//   -Mrecursion=examples/recursion/recursion.zig -Mcommon=tests/diff/common.zig
const common = @import("common");

// Pulls the "recursion" module into this compilation so its `export fn`s actually get emitted —
// `extern fn` below only declares symbols to link against, it doesn't import the module that
// defines them. Never referenced directly: all 4 functions are `export fn`, not `pub`.
const recursion = @import("recursion");
comptime {
    _ = recursion;
}

// gcd/isEven/isOdd/fact are all `export fn` without `pub` in recursion.zig: `export` gives them
// a C symbol but not cross-file visibility, so `recursion.gcd` etc. does not resolve. Declare
// them as `extern fn` instead (same rationale as basic.zig's scale/clampAdd/absDiff,
// tests/diff/basic/harness.zig).
extern fn gcd(a: u32, b: u32) u32;
extern fn isEven(n: u32) bool;
extern fn isOdd(n: u32) bool;
extern fn fact(n: u32) u32;

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn runGcd(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "recursion", "gcd", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u32 = @intCast(items[0].integer);
            const b: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(gcd)), .{ a, b }, gcd, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runIsEven(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "recursion", "isEven", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const n: u32 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(isEven)), .{n}, isEven, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runIsOdd(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "recursion", "isOdd", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const n: u32 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(isOdd)), .{n}, isOdd, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runFact(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "recursion", "fact", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const n: u32 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(fact)), .{n}, fact, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/recursion");

    try runGcd(gpa);
    try runIsEven(gpa);
    try runIsOdd(gpa);
    try runFact(gpa);
}
