//! floatops's differential-test dispatch (examples/floatops/floatops.zig: op16/op32/op64/
//! op80/op128, cmp64, divExact64). Shared runner code (fork/panic/render/JSONL plumbing) lives
//! in tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! Every float arg/result uses common.parseFloatHex/renderPayload's "0x" + hex-bits encoding
//! (docs/floats.md's diff protocol); `sel` is a plain int.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep floatops --dep common -Mroot=tests/diff/floatops/harness.zig \
//   -Mfloatops=examples/floatops/floatops.zig -Mcommon=tests/diff/common.zig
const floatops = @import("floatops");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn runOp(gpa: std.mem.Allocator, comptime T: type, comptime name: []const u8, comptime func: anytype) !void {
    try common.forEachLine(gpa, "floatops", name, struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const sel: u8 = @intCast(items[0].integer);
            const a = common.parseFloatHex(T, items[1].string);
            const b = common.parseFloatHex(T, items[2].string);
            const c = common.parseFloatHex(T, items[3].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(func)), .{ sel, a, b, c }, func, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runCmp64(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floatops", "cmp64", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.parseFloatHex(f64, items[0].string);
            const b = common.parseFloatHex(f64, items[1].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(floatops.cmp64)), .{ a, b }, floatops.cmp64, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runDivExact64(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "floatops", "divExact64", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a = common.parseFloatHex(f64, items[0].string);
            const b = common.parseFloatHex(f64, items[1].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(floatops.divExact64)), .{ a, b }, floatops.divExact64, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/floatops");

    try runOp(gpa, f16, "op16", floatops.op16);
    try runOp(gpa, f32, "op32", floatops.op32);
    try runOp(gpa, f64, "op64", floatops.op64);
    try runOp(gpa, f80, "op80", floatops.op80);
    try runOp(gpa, f128, "op128", floatops.op128);
    try runCmp64(gpa);
    try runDivExact64(gpa);
}
