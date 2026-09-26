//! Self-check for tests/diff/libm/libm.zig: compares the archive's air2lean_libm_* symbols
//! against Zig's own @sin/@cos/... builtins, in the same binary, over a handful of finite
//! positive samples per width. A mismatch means libm.zig's compiler_rt call resolved to a
//! different implementation than the compiler emits inline for the same op — e.g. the system
//! libm, bound in by symbol collision instead of compiler_rt.
//!
//! Linux: a mismatch is fatal (std.process.exit(1)) — the real check, run in CI. Elsewhere (e.g.
//! a local macOS run): informational only, a summary line, never fatal — non-Linux symbol
//! resolution and libm availability are not what this project ships on.
//!
//! Build (scripts/diff.sh, right after the archive; the archive is linked in as an extra input,
//! not a `--dep`, since this file resolves each symbol by name via @extern rather than importing
//! libm.zig as a module):
//!   zig build-exe -OReleaseSafe -mcpu=baseline --name libm_selfcheck \
//!     -femit-bin=<out> tests/diff/libm/selfcheck.zig <archive path>

const std = @import("std");
const builtin = @import("builtin");

const ops = [_][]const u8{ "sin", "cos", "tan", "exp", "exp2", "log", "log2", "log10" };
const narrow_widths = .{
    .{ "f16", f16 },
    .{ "f32", f32 },
    .{ "f64", f64 },
};
const wide_widths = .{
    .{ "f80", f80 },
    .{ "f128", f128 },
};

// A few finite, positive samples: enough to catch a wrong-implementation binding, small enough
// to also fit log/log2/log10's domain (positive) without a NaN result on either side.
fn samples(comptime T: type) [8]T {
    return .{ 0.1, 0.5, 1.0, 1.5, 2.0, 3.14159, 5.0, 10.0 };
}

fn builtinCall(comptime op: []const u8, comptime T: type, x: T) T {
    if (comptime std.mem.eql(u8, op, "sin")) return @sin(x);
    if (comptime std.mem.eql(u8, op, "cos")) return @cos(x);
    if (comptime std.mem.eql(u8, op, "tan")) return @tan(x);
    if (comptime std.mem.eql(u8, op, "exp")) return @exp(x);
    if (comptime std.mem.eql(u8, op, "exp2")) return @exp2(x);
    if (comptime std.mem.eql(u8, op, "log")) return @log(x);
    if (comptime std.mem.eql(u8, op, "log2")) return @log2(x);
    if (comptime std.mem.eql(u8, op, "log10")) return @log10(x);
    @compileError("libm self-check: unknown op " ++ op);
}

fn checkNarrow(comptime op: []const u8, comptime width: []const u8, comptime T: type, mismatches: *usize, total: *usize) void {
    const sym = "air2lean_libm_" ++ op ++ "_" ++ width;
    const archive: *const fn (u64) callconv(.c) u64 = @extern(*const fn (u64) callconv(.c) u64, .{ .name = sym });
    const Bits = std.meta.Int(.unsigned, @bitSizeOf(T));
    for (samples(T)) |x| {
        total.* += 1;
        const xbits: Bits = @bitCast(x);
        const got: Bits = @truncate(archive(xbits));
        const want: Bits = @bitCast(builtinCall(op, T, x));
        if (got != want) {
            mismatches.* += 1;
            std.debug.print("MISMATCH {s}: x-bits=0x{x} archive=0x{x} builtin=0x{x}\n", .{ sym, xbits, got, want });
        }
    }
}

fn checkWide(comptime op: []const u8, comptime width: []const u8, comptime T: type, mismatches: *usize, total: *usize) void {
    const hi_sym = "air2lean_libm_" ++ op ++ "_" ++ width ++ "_hi";
    const lo_sym = "air2lean_libm_" ++ op ++ "_" ++ width ++ "_lo";
    const archive_hi: *const fn (u64, u64) callconv(.c) u64 = @extern(*const fn (u64, u64) callconv(.c) u64, .{ .name = hi_sym });
    const archive_lo: *const fn (u64, u64) callconv(.c) u64 = @extern(*const fn (u64, u64) callconv(.c) u64, .{ .name = lo_sym });
    const Bits = std.meta.Int(.unsigned, @bitSizeOf(T));
    for (samples(T)) |x| {
        total.* += 1;
        const xbits: Bits = @bitCast(x);
        const hi: u64 = @truncate(@as(u128, xbits) >> 64);
        const lo: u64 = @truncate(xbits);
        const got: Bits = @truncate((@as(u128, archive_hi(hi, lo)) << 64) | archive_lo(hi, lo));
        const want: Bits = @bitCast(builtinCall(op, T, x));
        if (got != want) {
            mismatches.* += 1;
            std.debug.print("MISMATCH {s}/{s}: x-bits=0x{x} archive=0x{x} builtin=0x{x}\n", .{ hi_sym, lo_sym, xbits, got, want });
        }
    }
}

pub fn main() void {
    var mismatches: usize = 0;
    var total: usize = 0;
    inline for (ops) |op| {
        inline for (narrow_widths) |nw| checkNarrow(op, nw[0], nw[1], &mismatches, &total);
        inline for (wide_widths) |ww| checkWide(op, ww[0], ww[1], &mismatches, &total);
    }
    std.debug.print("libm self-check: {d}/{d} matched, {d} mismatched\n", .{ total - mismatches, total, mismatches });
    if (mismatches != 0 and builtin.os.tag == .linux) {
        std.process.exit(1);
    }
}
