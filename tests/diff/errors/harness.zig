//! errors's differential-test dispatch (examples/errors/errors.zig: parseDigit, sumDigits,
//! digitOrZero). Shared runner code (fork/panic/render/JSONL plumbing) lives in
//! tests/diff/common.zig; see its doc comment for the build command and protocol.
//!
//! parseDigit/sumDigits return `error{NotDigit}!T`: common.forkCall/renderPayload write
//! `{"ok":{"err":"NotDigit"}}` or the plain value (docs/generated-code.md's error-union rule).
//! None of the three ever panics (parseDigit's own bounds check guards the one subtraction that
//! could otherwise misbehave; digitOrZero and sumDigits both funnel through it).
//!
//! The Lean side cannot translate errors.zig yet (`is_non_err`/error-union handling is an
//! unsupported AIR tag in the translator, hit even by digitOrZero's plain `u8` signature since
//! it uses `catch` internally), so this harness builds and runs standalone; scripts/diff.sh only
//! compares its output once `AIR2LEAN_EXAMPLES` includes `errors` and the Lean side catches up.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep errors --dep common -Mroot=tests/diff/errors/harness.zig \
//   -Merrors=examples/errors/errors.zig -Mcommon=tests/diff/common.zig
const errors = @import("errors");
const common = @import("common");

// digitOrZero is `export fn` without `pub` in errors.zig: `export` gives it a C symbol but not
// cross-file visibility, so `errors.digitOrZero` does not resolve. Declare it as `extern fn`
// instead (same rationale as basic.zig's scale/clampAdd/absDiff, tests/diff/basic/harness.zig).
extern fn digitOrZero(c: u8) u8;

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

fn runParseDigit(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "errors", "parseDigit", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const c: u8 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(errors.parseDigit)), .{c}, errors.parseDigit, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runSumDigits(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "errors", "sumDigits", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const s_json = items[0].array.items;
            const s = try a.alloc(u8, s_json.len);
            defer a.free(s);
            for (s_json, 0..) |v, i| s[i] = @intCast(v.integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(errors.sumDigits)), .{s}, errors.sumDigits, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runDigitOrZero(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "errors", "digitOrZero", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const c: u8 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(digitOrZero)), .{c}, digitOrZero, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig/errors");

    try runParseDigit(gpa);
    try runSumDigits(gpa);
    try runDigitOrZero(gpa);
}
