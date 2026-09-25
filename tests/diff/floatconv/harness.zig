//! floatconv's differential-test dispatch (examples/floatconv/floatconv.zig: toI32, toU64,
//! toByte, fromI64, fromU128, f64ToF16, f16ToF128, f80ToF64, bits32, ofBits64). Shared runner
//! code (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment
//! for the build command and protocol.
//!
//! A float arg uses common.parseFloatHex's "0x" + hex-bits encoding. A >= 64-bit plain-int arg
//! (fromI64, fromU128, ofBits64) is a quoted decimal string instead (tests/diff/gen_inputs.zig's
//! doc comment on the section that writes them) — parsed with std.fmt.parseInt.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep floatconv --dep common -Mroot=tests/diff/floatconv/harness.zig \
//   -Mfloatconv=examples/floatconv/floatconv.zig -Mcommon=tests/diff/common.zig
const floatconv = @import("floatconv");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn runFloatArg(gpa: std.mem.Allocator, comptime FromT: type, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool) !void {
    try common.forEachLine(gpa, "floatconv", name, struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x = common.parseFloatHex(FromT, items[0].string);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(func)), .{x}, func, quote_wide);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runIntArg(gpa: std.mem.Allocator, comptime FromT: type, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool) !void {
    try common.forEachLine(gpa, "floatconv", name, struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x = std.fmt.parseInt(FromT, items[0].string, 10) catch unreachable;
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(func)), .{x}, func, quote_wide);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/floatconv");

    try runFloatArg(gpa, f64, "toI32", floatconv.toI32, false);
    try runFloatArg(gpa, f32, "toU64", floatconv.toU64, true); // u64 result: wide
    try runFloatArg(gpa, f32, "toByte", floatconv.toByte, false);
    try runIntArg(gpa, i64, "fromI64", floatconv.fromI64, false);
    try runIntArg(gpa, u128, "fromU128", floatconv.fromU128, false);
    try runFloatArg(gpa, f64, "f64ToF16", floatconv.f64ToF16, false);
    try runFloatArg(gpa, f16, "f16ToF128", floatconv.f16ToF128, false);
    try runFloatArg(gpa, f80, "f80ToF64", floatconv.f80ToF64, false);
    try runFloatArg(gpa, f32, "bits32", floatconv.bits32, false);
    try runIntArg(gpa, u64, "ofBits64", floatconv.ofBits64, false);
}
