//! variants's differential-test dispatch (examples/variants/variants.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! An enum argument is its tag value; a `Shape` argument is an object with its active field
//! (tests/diff/gen_inputs.zig). Results render through common.renderPayload: an enum as its tag
//! value, a `Shape` as the same object form.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep variants --dep common -Mroot=tests/diff/variants/harness.zig \
//   -Mvariants=examples/variants/variants.zig -Mcommon=tests/diff/common.zig
const variants = @import("variants");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn int(comptime T: type, v: std.json.Value) T {
    return @intCast(v.integer);
}

fn shapeOf(v: std.json.Value) variants.Shape {
    var it = v.object.iterator();
    const e = it.next().?;
    const name = e.key_ptr.*;
    const p = e.value_ptr.*;
    if (std.mem.eql(u8, name, "circle")) return .{ .circle = int(u32, p) };
    if (std.mem.eql(u8, name, "square")) return .{ .square = int(u32, p) };
    if (std.mem.eql(u8, name, "empty")) return .empty;
    return .{ .rect = .{ .w = int(u32, p.object.get("w").?), .h = int(u32, p.object.get("h").?) } };
}

/// Runs `func` on each input line of `name`; `args` builds its argument tuple from the line.
fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool, comptime args: anytype) !void {
    try common.forEachLine(gpa, "variants", name, struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            const outcome = try common.forkCall(Args, try args(a, items), func, quote_wide);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argLight(_: std.mem.Allocator, items: []std.json.Value) !struct { variants.Light } {
    return .{@enumFromInt(int(u8, items[0]))};
}
fn argLightN(_: std.mem.Allocator, items: []std.json.Value) !struct { variants.Light, u32 } {
    return .{ @enumFromInt(int(u8, items[0])), int(u32, items[1]) };
}
fn argPrio(_: std.mem.Allocator, items: []std.json.Value) !struct { variants.Prio } {
    return .{@enumFromInt(int(i8, items[0]))};
}
fn argU8(_: std.mem.Allocator, items: []std.json.Value) !struct { u8 } {
    return .{int(u8, items[0])};
}
fn argCode(_: std.mem.Allocator, items: []std.json.Value) !struct { variants.Code } {
    return .{@enumFromInt(int(u8, items[0]))};
}
fn argShape(_: std.mem.Allocator, items: []std.json.Value) !struct { variants.Shape } {
    return .{shapeOf(items[0])};
}
fn argShapeK(_: std.mem.Allocator, items: []std.json.Value) !struct { variants.Shape, u32 } {
    return .{ shapeOf(items[0]), int(u32, items[1]) };
}
fn argShapes(a: std.mem.Allocator, items: []std.json.Value) !struct { []const variants.Shape } {
    const js = items[0].array.items;
    const shapes = try a.alloc(variants.Shape, js.len);
    for (js, 0..) |j, i| shapes[i] = shapeOf(j);
    return .{shapes};
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    // `argShapes` allocates per line; an arena per run frees it all at the end.
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try common.makePath("tests/diff/out/zig/variants");

    try run(gpa, "next", variants.next, false, argLight);
    try run(gpa, "advance", variants.advance, false, argLightN);
    try run(gpa, "lightOf", variants.lightOf, false, argU8);
    try run(gpa, "prioValue", variants.prioValue, false, argPrio);
    try run(gpa, "isUrgent", variants.isUrgent, false, argPrio);
    try run(gpa, "severity", variants.severity, false, argCode);
    try run(gpa, "codeOf", variants.codeOf, false, argU8);
    try run(gpa, "area", variants.area, true, argShape);
    try run(arena, "totalArea", variants.totalArea, true, argShapes);
    try run(gpa, "scale", variants.scale, false, argShapeK);
    try run(gpa, "radius", variants.radius, false, argShape);
    try run(gpa, "isRound", variants.isRound, false, argShape);
}
