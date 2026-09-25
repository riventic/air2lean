//! floats's differential-test dispatch (examples/floats/floats.zig: lerp, clamp, isNan, hypot2,
//! celsius, dot). Shared runner code (fork/panic/render/JSONL plumbing) lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! celsius returns `?f32`: common.forkCall/renderPayload write `{"ok":null}` or the float's own
//! hex rendering. dot's two slice args are JSON arrays of float hex strings (docs/floats.md).

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep floats --dep common -Mroot=tests/diff/floats/harness.zig \
//   -Mfloats=examples/floats/floats.zig -Mcommon=tests/diff/common.zig
const floats = @import("floats");
const common = @import("common");

// lerp/clamp/isNan/hypot2 are `export fn` without `pub` in floats.zig: `export` gives them a C
// symbol but not cross-file visibility, so `floats.lerp` etc. does not resolve. Declare them as
// `extern fn` instead — same reasoning as tests/diff/basic/harness.zig's scale/clampAdd/absDiff.
extern fn lerp(a: f64, b: f64, t: f64) f64;
extern fn clamp(x: f32, lo: f32, hi: f32) f32;
extern fn isNan(x: f64) bool;
extern fn hypot2(a: f64, b: f64) f64;

// This is the compilation's root module (see the build command above), so this governs
// floats.zig too — Zig picks the panic override by shape on the root module, not per-module.
pub const panic = common.panic;

fn runLerp(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floats", "lerp", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.parseFloatHex(f64, items[0].string);
            const b = common.parseFloatHex(f64, items[1].string);
            const t = common.parseFloatHex(f64, items[2].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(lerp)), .{ a, b, t }, lerp, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runClamp(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floats", "clamp", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x = common.parseFloatHex(f32, items[0].string);
            const lo = common.parseFloatHex(f32, items[1].string);
            const hi = common.parseFloatHex(f32, items[2].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(clamp)), .{ x, lo, hi }, clamp, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runIsNan(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floats", "isNan", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x = common.parseFloatHex(f64, items[0].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(isNan)), .{x}, isNan, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runHypot2(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floats", "hypot2", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.parseFloatHex(f64, items[0].string);
            const b = common.parseFloatHex(f64, items[1].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(hypot2)), .{ a, b }, hypot2, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runCelsius(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floats", "celsius", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const k = common.parseFloatHex(f32, items[0].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(floats.celsius)), .{k}, floats.celsius, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn f64SliceFromJson(a: std.mem.Allocator, v: std.json.Value) ![]f64 {
    const items = v.array.items;
    const xs = try a.alloc(f64, items.len);
    for (items, 0..) |it, i| xs[i] = common.parseFloatHex(f64, it.string);
    return xs;
}

fn runDot(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floats", "dot", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const xs = try f64SliceFromJson(a, items[0]);
            defer a.free(xs);
            const ys = try f64SliceFromJson(a, items[1]);
            defer a.free(ys);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(floats.dot)), .{ xs, ys }, floats.dot, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/floats");

    try runLerp(gpa);
    try runClamp(gpa);
    try runIsNan(gpa);
    try runHypot2(gpa);
    try runCelsius(gpa);
    try runDot(gpa);
}
