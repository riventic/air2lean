//! Shared differential-test Zig-side runner code (docs/generated-code.md), imported as the
//! `common` module by each `tests/diff/<ex>/harness.zig`. Build with the STOCK system zig
//! (scripts/diff.sh does this):
//!   zig build-exe -OReleaseSafe -mcpu=baseline -femit-bin=<out> \
//!     --dep <ex> --dep common -Mroot=tests/diff/<ex>/harness.zig \
//!     -M<ex>=examples/<ex>/<ex>.zig -Mcommon=tests/diff/common.zig
//! ReleaseSafe applies to the whole compilation unit, so `<ex>.zig`'s own overflow/bounds checks
//! stay active — the same semantics the AIR exporter captured.
//!
//! Reads `tests/diff/<ex>/inputs/<fn>.jsonl` (tests/diff/gen_inputs.zig), calls the real
//! function for each input, and writes `tests/diff/out/zig/<ex>/<fn>.jsonl`: one line per
//! input, `{"ok": <result>}` or `{"fail": "<kind>"}`. A safety panic exits the child process
//! (each call runs in its own fork, so one panic never crashes the run) after it writes which
//! check tripped (see `panic` below).
//!
//! `<result>` follows docs/generated-code.md's diff protocol: a plain int is a bare or quoted
//! decimal (quoted for usize/u64 — `quote_wide`, since those can exceed a JS-safe integer); a
//! `bool` is `0`/`1`; a `?T` is `null` or T's own rendering; an `E!T` is `{"err":"<name>"}` or
//! T's own rendering. `renderPayload` below builds this text directly from the real Zig return
//! value, so nesting (e.g. none of today's examples return `?E!T`, but the rule composes) falls
//! out for free.
//!
//! `<kind>` is a `std.builtin.panic` member name — `outOfBounds`, `integerOverflow`, … (see
//! `panic` below, docs/generated-code.md §Panics) — or `unknown` if the child died without
//! reporting one (a signal, not a checked safety panic). scripts/diff.sh maps each kind to the
//! `Zig.Error` constructor the Lean side is expected to throw for the same check.
//!
//! A root module wires this in with `pub const panic = common.panic;` — Zig's panic override is
//! chosen by shape (`std.debug.FullPanic` / `std.debug.no_panic`) on the root module, not by an
//! interface, so a re-exporting `pub const` declaration in the actual root file is enough.

const std = @import("std");

/// Longest name in `panic` below (`integerPartOutOfBounds` / `exactDivisionRemainder`, 22
/// bytes) plus headroom; also sized to fit the longest ok-payload this protocol writes (a quoted
/// u64: `"18446744073709551615"`, 23 bytes) — it doubles as the parent's read buffer, which
/// doesn't know in advance whether the child reports a value or a panic kind.
const max_out_len = 64;

pub const Outcome = union(enum) {
    ok: struct { buf: [max_out_len]u8, len: usize },
    fail: struct { buf: [max_out_len]u8, len: usize },
};

fn failOutcome(kind: []const u8) Outcome {
    var f: Outcome = .{ .fail = .{ .buf = undefined, .len = kind.len } };
    @memcpy(f.fail.buf[0..kind.len], kind);
    return f;
}

/// Set to the write end of the result pipe by the child right after `fork()`, so `panic` below
/// can report which safety check tripped without threading state through `@call`.
var panic_fd: std.posix.fd_t = -1;

/// Installed as this binary's `std.builtin.panic` (see `panic` below): reports `kind` to the
/// parent and exits nonzero, so a safety panic in the child becomes a normal `waitpid` exit
/// status instead of a signal. Best-effort write — a failed write is no worse than the
/// zero-bytes case the parent already treats as `unknown`.
fn reportPanic(kind: []const u8) noreturn {
    // The parent (not a forked child) panicked: a harness bug, not a tested outcome. Say so.
    // Not `std.debug.panic`: that calls this override again.
    if (panic_fd < 0) {
        std.debug.print("harness panic outside a child: {s}\n", .{kind});
        std.posix.abort();
    }
    _ = std.posix.write(panic_fd, kind) catch {};
    std.posix.exit(1);
}

/// Overrides Zig's default panic handler for the whole binary that imports it as its root
/// module's `panic` (see the module doc comment above). Member names/signatures must match
/// `std.debug.FullPanic` / `std.debug.no_panic` exactly; each one reports its own name via
/// `reportPanic` instead of printing a trace. docs/generated-code.md §Panics maps each name to
/// the `Zig.Error` constructor `Air2Lean/Emit.lean` emits for the matching check.
pub const panic = struct {
    pub fn call(_: []const u8, _: ?usize) noreturn {
        reportPanic("panic");
    }
    pub fn sentinelMismatch(_: anytype, _: anytype) noreturn {
        reportPanic("sentinelMismatch");
    }
    pub fn unwrapError(_: anyerror) noreturn {
        reportPanic("unwrapError");
    }
    pub fn outOfBounds(_: usize, _: usize) noreturn {
        reportPanic("outOfBounds");
    }
    pub fn startGreaterThanEnd(_: usize, _: usize) noreturn {
        reportPanic("startGreaterThanEnd");
    }
    pub fn inactiveUnionField(_: anytype, _: anytype) noreturn {
        reportPanic("inactiveUnionField");
    }
    pub fn sliceCastLenRemainder(_: usize) noreturn {
        reportPanic("sliceCastLenRemainder");
    }
    pub fn reachedUnreachable() noreturn {
        reportPanic("reachedUnreachable");
    }
    pub fn unwrapNull() noreturn {
        reportPanic("unwrapNull");
    }
    pub fn castToNull() noreturn {
        reportPanic("castToNull");
    }
    pub fn incorrectAlignment() noreturn {
        reportPanic("incorrectAlignment");
    }
    pub fn invalidErrorCode() noreturn {
        reportPanic("invalidErrorCode");
    }
    pub fn integerOutOfBounds() noreturn {
        reportPanic("integerOutOfBounds");
    }
    pub fn integerOverflow() noreturn {
        reportPanic("integerOverflow");
    }
    pub fn shlOverflow() noreturn {
        reportPanic("shlOverflow");
    }
    pub fn shrOverflow() noreturn {
        reportPanic("shrOverflow");
    }
    pub fn divideByZero() noreturn {
        reportPanic("divideByZero");
    }
    pub fn exactDivisionRemainder() noreturn {
        reportPanic("exactDivisionRemainder");
    }
    pub fn integerPartOutOfBounds() noreturn {
        reportPanic("integerPartOutOfBounds");
    }
    pub fn corruptSwitch() noreturn {
        reportPanic("corruptSwitch");
    }
    pub fn shiftRhsTooBig() noreturn {
        reportPanic("shiftRhsTooBig");
    }
    pub fn invalidEnumValue() noreturn {
        reportPanic("invalidEnumValue");
    }
    pub fn forLenMismatch() noreturn {
        reportPanic("forLenMismatch");
    }
    pub fn copyLenMismatch() noreturn {
        reportPanic("copyLenMismatch");
    }
    pub fn memcpyAlias() noreturn {
        reportPanic("memcpyAlias");
    }
    pub fn noreturnReturned() noreturn {
        reportPanic("noreturnReturned");
    }
};

/// Writes `v`'s diff-protocol "ok" payload text (the part that goes inside `{"ok": ... }`) to
/// `writer`: bare/quoted decimal for an int leaf (`quote_wide` picks quoting — usize/u64 only),
/// `0`/`1` for bool, `null`/inner for `?T`, `{"err":"name"}`/inner for `E!T`, `"0x<bits>"` (or
/// `"nan"`) for a float leaf (docs/floats.md's diff protocol — every NaN, tested with `v != v`,
/// never bits, collapses to the one string `"nan"`). Recurses on `T`'s shape, so `?T`/`E!T`
/// nesting composes without new cases (no example needs it today).
fn renderPayload(comptime T: type, writer: anytype, quote_wide: bool, v: T) !void {
    switch (@typeInfo(T)) {
        .optional => {
            if (v) |inner| {
                try renderPayload(@TypeOf(inner), writer, quote_wide, inner);
            } else {
                try writer.writeAll("null");
            }
        },
        .error_union => {
            if (v) |ok_v| {
                try renderPayload(@TypeOf(ok_v), writer, quote_wide, ok_v);
            } else |err| {
                try writer.print("{{\"err\":\"{s}\"}}", .{@errorName(err)});
            }
        },
        .bool => try writer.print("{d}", .{@intFromBool(v)}),
        .int => if (quote_wide)
            try writer.print("\"{d}\"", .{v})
        else
            try writer.print("{d}", .{v}),
        .float => {
            if (v != v) {
                try writer.writeAll("\"nan\"");
            } else {
                const width = @bitSizeOf(T);
                const digits = std.fmt.comptimePrint("{d}", .{width / 4});
                const bits: std.meta.Int(.unsigned, width) = @bitCast(v);
                try writer.print("\"0x{x:0>" ++ digits ++ "}\"", .{bits});
            }
        },
        else => @compileError("renderPayload: unsupported type " ++ @typeName(T)),
    }
}

/// Parses a float diff-protocol input: `"0x"` + lowercase hex bits, zero-padded to
/// `width/4` digits (docs/generated-code.md, docs/floats.md). Inputs are always hex, never
/// `"nan"` — `tests/diff/gen_inputs.zig` encodes a NaN input as its bit pattern too.
pub fn parseFloatHex(comptime T: type, s: []const u8) T {
    const width = @bitSizeOf(T);
    const bits = std.fmt.parseInt(std.meta.Int(.unsigned, width), s[2..], 16) catch unreachable;
    return @bitCast(bits);
}

/// Runs `func(args)` in a forked child; the child never returns to this function on the parent
/// side. `Args` must be `std.meta.ArgsTuple(@TypeOf(func))`; `quote_wide` is forwarded to
/// `renderPayload` for `func`'s (possibly `?`/`!`-wrapped) int leaf. On success the child writes
/// its rendered ok-payload to a pipe and exits 0; on a safety panic, `panic` above writes the
/// tripped check's name to the same pipe and exits 1. The parent reports `.ok` only for a clean
/// exit with bytes; a nonzero exit with a reported name becomes `.fail` with that name; anything
/// else (a signal, or no bytes at all) becomes `.fail("unknown")`.
pub fn forkCall(comptime Args: type, args: Args, comptime func: anytype, quote_wide: bool) !Outcome {
    const fds = try std.posix.pipe();
    const pid = try std.posix.fork();
    if (pid == 0) {
        // Child: never returns. `panic_fd` lets `panic` above report a safety-check trip; the
        // stderr redirect below covers the unlikely case something still writes there (e.g. the
        // generic `panic.call` path) since that noise adds nothing over the `{"fail":...}` line
        // already recorded.
        std.posix.close(fds[0]);
        panic_fd = fds[1];
        if (std.fs.openFileAbsolute("/dev/null", .{ .mode = .write_only })) |devnull| {
            std.posix.dup2(devnull.handle, std.posix.STDERR_FILENO) catch {};
        } else |_| {}

        const raw = @call(.auto, func, args);
        var buf: [max_out_len]u8 = undefined;
        var fbs = std.io.fixedBufferStream(&buf);
        renderPayload(@TypeOf(raw), fbs.writer(), quote_wide, raw) catch unreachable;
        const text = fbs.getWritten();
        _ = std.posix.write(fds[1], text) catch {};
        std.posix.exit(0);
    }

    // Parent.
    std.posix.close(fds[1]);
    defer std.posix.close(fds[0]);
    var buf: [max_out_len]u8 = undefined;
    var total: usize = 0;
    while (total < buf.len) {
        const n = std.posix.read(fds[0], buf[total..]) catch break;
        if (n == 0) break;
        total += n;
    }
    const wr = std.posix.waitpid(pid, 0);
    const exited_ok = std.posix.W.IFEXITED(wr.status) and std.posix.W.EXITSTATUS(wr.status) == 0;
    const exited_fail = std.posix.W.IFEXITED(wr.status) and std.posix.W.EXITSTATUS(wr.status) != 0;
    if (exited_ok and total > 0) {
        var o: Outcome = .{ .ok = .{ .buf = undefined, .len = total } };
        @memcpy(o.ok.buf[0..total], buf[0..total]);
        return o;
    }
    if (exited_fail and total > 0) return failOutcome(buf[0..total]);
    return failOutcome("unknown");
}

pub fn writeResult(writer: anytype, outcome: Outcome) !void {
    switch (outcome) {
        .ok => |o| try writer.print("{{\"ok\":{s}}}\n", .{o.buf[0..o.len]}),
        .fail => |f| try writer.print("{{\"fail\":\"{s}\"}}\n", .{f.buf[0..f.len]}),
    }
}

/// Reads `tests/diff/<ex>/inputs/<name>.jsonl`, opens `tests/diff/out/zig/<ex>/<name>.jsonl`,
/// and calls `perLine` for each non-empty input line with the parsed JSON array and the output
/// writer.
pub fn forEachLine(
    gpa: std.mem.Allocator,
    comptime ex: []const u8,
    comptime name: []const u8,
    perLine: anytype,
) !void {
    const in_path = "tests/diff/" ++ ex ++ "/inputs/" ++ name ++ ".jsonl";
    const out_path = "tests/diff/out/zig/" ++ ex ++ "/" ++ name ++ ".jsonl";

    const content = try std.fs.cwd().readFileAlloc(gpa, in_path, 4 << 20);
    defer gpa.free(content);
    const out_file = try std.fs.cwd().createFile(out_path, .{});
    defer out_file.close();
    const writer = out_file.deprecatedWriter();

    var lines = std.mem.splitScalar(u8, content, '\n');
    while (lines.next()) |line| {
        if (line.len == 0) continue;
        var parsed = try std.json.parseFromSlice(std.json.Value, gpa, line, .{});
        defer parsed.deinit();
        try perLine(gpa, parsed.value.array.items, writer);
    }
}
