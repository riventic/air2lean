//! enums's differential-test dispatch (examples/enums/enums.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! An enum argument is its tag value; a `Shape` argument is an object with its active field
//! (tests/diff/gen_inputs.zig). Results render through common.renderPayload: an enum as its tag
//! value, a `Shape` as the same object form.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep enums --dep common -Mroot=tests/diff/enums/harness.zig \
//   -Menums=examples/enums/enums.zig -Mcommon=tests/diff/common.zig
const enums = @import("enums");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn int(comptime T: type, v: std.json.Value) T {
    return @intCast(v.integer);
}

fn shapeOf(v: std.json.Value) enums.Shape {
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
    try common.forEachLine(gpa, "enums", name, struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            const outcome = try common.forkCall(Args, try args(a, items), func, quote_wide);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argLight(_: std.mem.Allocator, items: []std.json.Value) !struct { enums.Light } {
    return .{@enumFromInt(int(u8, items[0]))};
}
fn argLightN(_: std.mem.Allocator, items: []std.json.Value) !struct { enums.Light, u32 } {
    return .{ @enumFromInt(int(u8, items[0])), int(u32, items[1]) };
}
fn argPrio(_: std.mem.Allocator, items: []std.json.Value) !struct { enums.Prio } {
    return .{@enumFromInt(int(i8, items[0]))};
}
fn argU8(_: std.mem.Allocator, items: []std.json.Value) !struct { u8 } {
    return .{int(u8, items[0])};
}
fn argCode(_: std.mem.Allocator, items: []std.json.Value) !struct { enums.Code } {
    return .{@enumFromInt(int(u8, items[0]))};
}
fn argShape(_: std.mem.Allocator, items: []std.json.Value) !struct { enums.Shape } {
    return .{shapeOf(items[0])};
}
fn argShapeK(_: std.mem.Allocator, items: []std.json.Value) !struct { enums.Shape, u32 } {
    return .{ shapeOf(items[0]), int(u32, items[1]) };
}
fn argShapes(a: std.mem.Allocator, items: []std.json.Value) !struct { []const enums.Shape } {
    const js = items[0].array.items;
    const shapes = try a.alloc(enums.Shape, js.len);
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

    try common.makePath("tests/diff/out/zig/enums");

    try run(gpa, "next", enums.next, false, argLight);
    try run(gpa, "advance", enums.advance, false, argLightN);
    try run(gpa, "lightOf", enums.lightOf, false, argU8);
    try run(gpa, "prioValue", enums.prioValue, false, argPrio);
    try run(gpa, "isUrgent", enums.isUrgent, false, argPrio);
    try run(gpa, "severity", enums.severity, false, argCode);
    try run(gpa, "codeOf", enums.codeOf, false, argU8);
    try run(gpa, "area", enums.area, true, argShape);
    try run(arena, "totalArea", enums.totalArea, true, argShapes);
    try run(gpa, "scale", enums.scale, false, argShapeK);
    try run(gpa, "radius", enums.radius, false, argShape);
    try run(gpa, "isRound", enums.isRound, false, argShape);
}
