//! basic's differential-test dispatch (docs/generated-code.md names the 8 functions). Shared
//! runner code (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc
//! comment for the build command and protocol. This file only has basic-specific glue: the
//! `Job` JSON parser and one small `runXxx` per function.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep basic --dep common -Mroot=tests/diff/basic/harness.zig \
//   -Mbasic=examples/basic/basic.zig -Mcommon=tests/diff/common.zig
const basic = @import("basic");
const common = @import("common");

// `scale`, `clampAdd`, `absDiff` are `export fn` without `pub` in basic.zig: `export` gives them
// a C symbol but not cross-file visibility, so `basic.scale` etc. does not resolve. Declare them
// as `extern fn` instead — `extern`/`export` default to the C calling convention, so these link
// directly against the symbols basic.zig already exports into this same executable.
extern fn scale(a: u32, b: u8) u32;
extern fn clampAdd(a: u16, b: u16) u16;
extern fn absDiff(a: i32, b: i32) u32;

// This is the compilation's root module (see the build command above), so this governs
// basic.zig too — Zig picks the panic override by shape on the root module, not per-module.
pub const panic = common.panic;

fn jobFromJson(v: std.json.Value) basic.Job {
    return .{
        .duration = @intCast(v.object.get("duration").?.integer),
        .due = @intCast(v.object.get("due").?.integer),
        .weight = @intCast(v.object.get("weight").?.integer),
    };
}

fn runScale(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "scale", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u32 = @intCast(items[0].integer);
            const b: u8 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(scale)), .{ a, b }, scale, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runClampAdd(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "clampAdd", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u16 = @intCast(items[0].integer);
            const b: u16 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(clampAdd)), .{ a, b }, clampAdd, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runAbsDiff(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "absDiff", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: i32 = @intCast(items[0].integer);
            const b: i32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(absDiff)), .{ a, b }, absDiff, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runTardiness(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "tardiness", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u32 = @intCast(items[0].integer);
            const b: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(basic.tardiness)), .{ a, b }, basic.tardiness, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runWeightedTardiness(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "weightedTardiness", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const job = jobFromJson(items[0]);
            const start: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(basic.weightedTardiness)), .{ job, start }, basic.weightedTardiness, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runSum(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "sum", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const xs_json = items[0].array.items;
            const xs = try a.alloc(u32, xs_json.len);
            defer a.free(xs);
            for (xs_json, 0..) |v, i| xs[i] = @intCast(v.integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(basic.sum)), .{xs}, basic.sum, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runTotalWeightedTardiness(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "totalWeightedTardiness", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const jobs_json = items[0].array.items;
            const jobs = try a.alloc(basic.Job, jobs_json.len);
            defer a.free(jobs);
            for (jobs_json, 0..) |jv, i| jobs[i] = jobFromJson(jv);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(basic.totalWeightedTardiness)), .{jobs}, basic.totalWeightedTardiness, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runClassify(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "basic", "classify", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x: u8 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(basic.classify)), .{x}, basic.classify, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/basic");

    try runScale(gpa);
    try runClampAdd(gpa);
    try runAbsDiff(gpa);
    try runTardiness(gpa);
    try runWeightedTardiness(gpa);
    try runSum(gpa);
    try runTotalWeightedTardiness(gpa);
    try runClassify(gpa);
}
