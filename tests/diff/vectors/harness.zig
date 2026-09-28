//! vectors's differential-test dispatch (examples/vectors/vectors.zig: fDot, uDotWrap, satAdd,
//! maxLane, reverse, checkedAdd, and the coverage functions splatAdd .. twiceInMem). Shared runner code (fork/panic/render/JSONL plumbing) lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! Every function here takes one or two `@Vector(4, T)` args; `common.vectorFromJson` parses
//! each from its JSON-array input line, and `common.renderPayload`'s `.vector` case renders a
//! `@Vector(4, T)` result the same way (docs/air-json.md's `elems` shape, reused for the diff
//! protocol).

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep vectors --dep common -Mroot=tests/diff/vectors/harness.zig \
//   -Mvectors=examples/vectors/vectors.zig -Mcommon=tests/diff/common.zig
const vectors = @import("vectors");
const common = @import("common");

// None of vectors.zig's functions are `pub` (see below), so nothing here otherwise references
// the `vectors` module; without a reference Zig never analyzes the file, and its `export fn`s
// never reach the link. This forces that analysis.
comptime {
    _ = vectors;
}

// fDot/uDotWrap/satAdd/maxLane/reverse/checkedAdd are `export fn` without `pub` in vectors.zig:
// `export` gives them a C symbol but not cross-file visibility, so `vectors.fDot` etc. does not
// resolve. Declare them as `extern fn` instead — same reasoning as tests/diff/basic/harness.zig's
// scale/clampAdd/absDiff.
extern fn fDot(a: @Vector(4, f32), b: @Vector(4, f32)) f32;
extern fn uDotWrap(a: @Vector(4, u32), b: @Vector(4, u32)) u32;
extern fn satAdd(a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32);
extern fn maxLane(v: @Vector(4, i32)) i32;
extern fn reverse(v: @Vector(4, u32)) @Vector(4, u32);
extern fn checkedAdd(a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32);
extern fn splatAdd(v: @Vector(4, u32), s: u32) @Vector(4, u32);
extern fn pick(m: @Vector(4, bool), a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32);
extern fn interleave(a: @Vector(4, u32), b: @Vector(4, u32)) @Vector(4, u32);
extern fn andLanes(v: @Vector(4, u32)) u32;
extern fn orLanes(v: @Vector(4, u32)) u32;
extern fn xorLanes(v: @Vector(4, u32)) u32;
extern fn minLane(v: @Vector(4, i32)) i32;
extern fn uMinLane(v: @Vector(4, u32)) u32;
extern fn fMin(v: @Vector(4, f32)) f32;
extern fn fMax(v: @Vector(4, f32)) f32;
extern fn twiceInMem(v: @Vector(4, u32)) @Vector(4, u32);

// This is the compilation's root module (see the build command above), so this governs
// vectors.zig too — Zig picks the panic override by shape on the root module, not per-module.
pub const panic = common.panic;

fn runFDot(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "vectors", "fDot", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.vectorFromJson(4, f32, items[0]);
            const b = common.vectorFromJson(4, f32, items[1]);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(fDot)), .{ a, b }, fDot, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runUDotWrap(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "vectors", "uDotWrap", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.vectorFromJson(4, u32, items[0]);
            const b = common.vectorFromJson(4, u32, items[1]);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(uDotWrap)), .{ a, b }, uDotWrap, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runSatAdd(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "vectors", "satAdd", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.vectorFromJson(4, u32, items[0]);
            const b = common.vectorFromJson(4, u32, items[1]);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(satAdd)), .{ a, b }, satAdd, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runMaxLane(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "vectors", "maxLane", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const v = common.vectorFromJson(4, i32, items[0]);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(maxLane)), .{v}, maxLane, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runReverse(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "vectors", "reverse", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const v = common.vectorFromJson(4, u32, items[0]);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(reverse)), .{v}, reverse, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runCheckedAdd(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "vectors", "checkedAdd", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.vectorFromJson(4, u32, items[0]);
            const b = common.vectorFromJson(4, u32, items[1]);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(checkedAdd)), .{ a, b }, checkedAdd, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

/// The coverage functions: each argument is one JSON item, parsed by its type.
fn runArgs(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype) !void {
    try common.forEachLine(gpa, "vectors", name, struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            var args: Args = undefined;
            inline for (@typeInfo(Args).@"struct".fields, 0..) |f, i| {
                args[i] = switch (@typeInfo(f.type)) {
                    .vector => |v| common.vectorFromJson(v.len, v.child, items[i]),
                    .int => @intCast(items[i].integer),
                    else => @compileError("runArgs: unsupported argument " ++ @typeName(f.type)),
                };
            }
            const outcome = try common.forkCall(Args, args, func, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/vectors");

    try runFDot(gpa);
    try runUDotWrap(gpa);
    try runSatAdd(gpa);
    try runMaxLane(gpa);
    try runReverse(gpa);
    try runCheckedAdd(gpa);
    try runArgs(gpa, "splatAdd", splatAdd);
    try runArgs(gpa, "pick", pick);
    try runArgs(gpa, "interleave", interleave);
    try runArgs(gpa, "andLanes", andLanes);
    try runArgs(gpa, "orLanes", orLanes);
    try runArgs(gpa, "xorLanes", xorLanes);
    try runArgs(gpa, "minLane", minLane);
    try runArgs(gpa, "uMinLane", uMinLane);
    try runArgs(gpa, "fMin", fMin);
    try runArgs(gpa, "fMax", fMax);
    try runArgs(gpa, "twiceInMem", twiceInMem);
}
