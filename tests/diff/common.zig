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
const compat = @import("compat.zig");

/// The child's output text: the rendered ok-payload or the panic kind. Any length (a result
/// with the input buffers can be long); `writeResult` frees it.
pub const OutcomeKind = enum { value, error_return, native_panic, native_signal, native_harness_failure, input_failure };
var metadata_writer: ?*std.Io.Writer = null;

pub const Outcome = union(enum) {
    ok: struct { payload: []u8, kind: OutcomeKind },
    fail: struct { name: []u8, kind: OutcomeKind },
};

const out_gpa = std.heap.page_allocator;

fn harnessFailure() Outcome {
    return .{ .fail = .{
        .name = out_gpa.dupe(u8, "unknown") catch @panic("out of memory"),
        .kind = .native_harness_failure,
    } };
}

/// The input buffers of a function that uses memory (docs/generated-code.md §Differential test):
/// each 16-byte aligned, like the blocks that `tests/diff/Diff.lean` makes for them.
pub const Buf = []align(16) u8;

/// Set by the child before it renders a result: `renderPayload` writes a pointer as its buffer
/// index and offset in these buffers.
var render_bufs: []const Buf = &.{};

/// The allocator of a function that takes a `std.mem.Allocator`, with the rules of the model
/// (`ZigLean/Mem/Alloc.lean`, docs/std-models.md): allocation number `fail_at` (from 0) fails, and
/// so does an allocation of more than `max_alloc_bytes` bytes; `resize` and `remap` always fail;
/// a free of memory that is not a live allocation of the same length panics with the kind
/// `doubleFree`.
pub const TestAllocator = struct {
    fail_at: ?usize = null,
    failures: []const usize = &.{},
    request_cap: usize = max_alloc_bytes,
    count: usize = 0,
    live: std.ArrayListUnmanaged([]u8) = .empty,

    pub const max_alloc_bytes = 1 << 20;

    /// Decode an explicit reference-model policy. The caller owns `failures` when nonempty.
    /// Legacy null/integer inputs preserve the original differential corpus.
    pub fn fromJson(gpa: std.mem.Allocator, value: std.json.Value) !TestAllocator {
        if (value == .null) return .{};
        if (value == .integer) return .{ .fail_at = try policyNat(value) };
        if (value != .object) return error.InvalidAllocatorPolicy;
        var result: TestAllocator = .{};
        if (value.object.get("fail_at")) |v| {
            if (v != .null) result.fail_at = try policyNat(v);
        }
        if (value.object.get("max_bytes")) |v| result.request_cap = try policyNat(v);
        if (value.object.get("failures")) |v| {
            if (v != .array) return error.InvalidAllocatorPolicy;
            const failures = try gpa.alloc(usize, v.array.items.len);
            errdefer gpa.free(failures);
            for (v.array.items, 0..) |item, i| failures[i] = try policyNat(item);
            result.failures = failures;
        }
        return result;
    }

    fn policyNat(value: std.json.Value) !usize {
        if (value != .integer or value.integer < 0) return error.InvalidAllocatorPolicy;
        return std.math.cast(usize, value.integer) orelse error.InvalidAllocatorPolicy;
    }

    pub fn allocator(self: *TestAllocator) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{
            .alloc = alloc,
            .resize = resize,
            .remap = remap,
            .free = free,
        } };
    }

    fn alloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *TestAllocator = @ptrCast(@alignCast(ctx));
        const k = self.count;
        self.count += 1;
        if (self.fail_at == k or len > self.request_cap or std.mem.indexOfScalar(usize, self.failures, k) != null) return null;
        const p = out_gpa.rawAlloc(len, alignment, ret_addr) orelse reportHarnessFailure("harnessOutOfMemory");
        self.live.append(out_gpa, p[0..len]) catch reportHarnessFailure("harnessOutOfMemory");
        return p;
    }

    fn resize(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) bool {
        return false;
    }

    fn remap(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) ?[*]u8 {
        return null;
    }

    fn free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const self: *TestAllocator = @ptrCast(@alignCast(ctx));
        for (self.live.items, 0..) |m, i| {
            if (m.ptr == memory.ptr and m.len == memory.len) {
                _ = self.live.swapRemove(i);
                out_gpa.rawFree(memory, alignment, ret_addr);
                return;
            }
        }
        reportPanic("doubleFree");
    }
};

/// The allocator of the call that the child runs, if the function takes one: the child also
/// writes the number of live allocations after the call, `,"live":<n>`.
pub var test_alloc: ?*TestAllocator = null;

fn writeAll(fd: std.posix.fd_t, bytes: []const u8) void {
    var done: usize = 0;
    while (done < bytes.len) done += compat.write(fd, bytes[done..]) catch return;
}

/// Set to the write end of the result pipe by the child right after `fork()`, so `panic` below
/// can report which safety check tripped without threading state through `@call`.
var panic_fd: std.posix.fd_t = -1;

/// Installed as this binary's `std.builtin.panic` (see `panic` below): reports `kind` to the
/// parent and exits nonzero, so a safety panic in the child becomes a normal `waitpid` exit
/// status instead of a signal. Best-effort write — a failed write is no worse than the
/// zero-bytes case the parent already treats as `unknown`.
fn reportPanic(kind: []const u8) noreturn {
    reportChildFailure(kind, 'P');
}

fn reportHarnessFailure(kind: []const u8) noreturn {
    reportChildFailure(kind, 'H');
}

fn reportChildFailure(kind: []const u8, tag: u8) noreturn {
    // The parent (not a forked child) panicked: a harness bug, not a tested outcome. Say so.
    // Not `std.debug.panic`: that calls this override again.
    if (panic_fd < 0) {
        std.debug.print("harness panic outside a child: {s}\n", .{kind});
        compat.abort();
    }
    writeAll(panic_fd, &.{tag});
    writeAll(panic_fd, kind);
    compat.exit(1);
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
    // Members added in Zig 0.17.0; earlier versions do not look them up.
    pub fn unexpectedErrorCode(_: anyerror) noreturn {
        reportPanic("unexpectedErrorCode");
    }
    pub fn loadUninstantiableType() noreturn {
        reportPanic("loadUninstantiableType");
    }
};

/// Writes `v`'s diff-protocol "ok" payload text (the part that goes inside `{"ok": ... }`) to
/// `writer`: bare/quoted decimal for an int leaf (`quote_wide` picks quoting — usize/u64 only),
/// `0`/`1` for bool, `null`/inner for `?T`, `{"err":"name"}`/inner for `E!T`, `"0x<bits>"` (or
/// `"nan"`) for a float leaf (docs/floats.md's diff protocol — every NaN, tested with `v != v`,
/// never bits, collapses to the one string `"nan"`), the tag value for an enum, and objects for
/// a union and a struct (below), and a JSON array (lane 0 first) for a `@Vector(n, T)`.
/// Recurses on `T`'s shape, so `?T`/`E!T` nesting composes without new cases (no example needs
/// it today).
/// Inspect the returned value, rather than infer source errors from rendered text.
fn returnedError(comptime T: type, value: T) bool {
    return switch (@typeInfo(T)) {
        .error_union => if (value) |v| returnedError(@TypeOf(v), v) else |_| true,
        .optional => if (value) |v| returnedError(@TypeOf(v), v) else false,
        else => false,
    };
}

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
                const bits: compat.Bits(T) = @bitCast(v);
                try writer.print("\"0x{x:0>" ++ digits ++ "}\"", .{bits});
            }
        },
        // An enum is its tag value; a union is `{"<active field>":<payload>}` (`null` for a
        // field without payload); a struct is `{"<field>":<value>,…}` in field order.
        .@"enum" => try writer.print("{d}", .{@intFromEnum(v)}),
        .@"union" => switch (v) {
            inline else => |payload, tag| {
                try writer.print("{{\"{s}\":", .{@tagName(tag)});
                try renderPayload(@TypeOf(payload), writer, quote_wide, payload);
                try writer.writeAll("}");
            },
        },
        .@"struct" => {
            try writer.writeAll("{");
            inline for (0..comptime compat.fieldCount(T)) |i| {
                const name = comptime compat.fieldName(T, i);
                if (i > 0) try writer.writeAll(",");
                try writer.print("\"{s}\":", .{name});
                try renderPayload(compat.FieldType(T, i), writer, quote_wide, @field(v, name));
            }
            try writer.writeAll("}");
        },
        // `@Vector(n, T)`: a JSON array of `n` lanes, lane 0 first (Zig's lane order).
        .vector => |vi| {
            try writer.writeAll("[");
            inline for (0..vi.len) |i| {
                if (i > 0) try writer.writeAll(",");
                try renderPayload(vi.child, writer, quote_wide, v[i]);
            }
            try writer.writeAll("]");
        },
        .void => try writer.writeAll("null"),
        // A pointer into the input buffers is `{"buf":<index>,"off":<offset>}`, a slice also has
        // `"len"`. A pointer to other memory (a global) is `{"bytes":"<hex>"}`: the bytes of the
        // value, or of the items of a slice.
        .pointer => |p| {
            const addr = switch (p.size) {
                .one => @intFromPtr(v),
                .slice => @intFromPtr(v.ptr),
                else => @compileError("renderPayload: unsupported pointer " ++ @typeName(T)),
            };
            for (render_bufs, 0..) |b, i| {
                const base = @intFromPtr(b.ptr);
                if (addr >= base and addr <= base + b.len) {
                    try writer.print("{{\"buf\":{d},\"off\":{d}", .{ i, addr - base });
                    if (p.size == .slice) try writer.print(",\"len\":{d}", .{v.len});
                    try writer.writeAll("}");
                    return;
                }
            }
            const bytes = if (p.size == .slice) std.mem.sliceAsBytes(v) else std.mem.asBytes(v);
            try writer.writeAll("{\"bytes\":\"");
            for (bytes) |byte| try writer.print("{x:0>2}", .{byte});
            try writer.writeAll("\"}");
        },
        else => @compileError("renderPayload: unsupported type " ++ @typeName(T)),
    }
}

/// Parses a float diff-protocol input: `"0x"` + lowercase hex bits, zero-padded to
/// `width/4` digits (docs/generated-code.md, docs/floats.md). Inputs are always hex, never
/// `"nan"` — `tests/diff/gen_inputs.zig` encodes a NaN input as its bit pattern too.
pub fn parseFloatHex(comptime T: type, s: []const u8) T {
    const bits = std.fmt.parseInt(compat.Bits(T), s[2..], 16) catch unreachable;
    return @bitCast(bits);
}

/// Parses a `@Vector(n, T)` diff-protocol input: a JSON array of `n` lanes (the same shape
/// `tests/diff/gen_inputs.zig` writes, and docs/air-json.md's `elems` shape). A float lane is
/// `parseFloatHex`'s hex string; an int lane is a bare JSON integer, positive or negative.
pub fn vectorFromJson(comptime n: usize, comptime T: type, v: std.json.Value) @Vector(n, T) {
    // An array, then one conversion: 0.16.0 has no store to a vector lane at a runtime index.
    var lanes: [n]T = undefined;
    for (v.array.items, 0..) |item, i| {
        lanes[i] = switch (@typeInfo(T)) {
            .float => parseFloatHex(T, item.string),
            .int => @intCast(item.integer),
            .bool => item.bool,
            else => @compileError("vectorFromJson: unsupported lane type " ++ @typeName(T)),
        };
    }
    return lanes;
}

/// Runs `func(args)` in a forked child; the child never returns to this function on the parent
/// side. `Args` must be `std.meta.ArgsTuple(@TypeOf(func))`; `quote_wide` is forwarded to
/// `renderPayload` for `func`'s (possibly `?`/`!`-wrapped) int leaf. On success the child writes
/// its rendered ok-payload to a pipe and exits 0; on a safety panic, `panic` above writes the
/// tripped check's name to the same pipe and exits 1. The parent reports `.ok` only for a clean
/// exit with bytes; a nonzero exit with a reported name becomes `.fail` with that name; anything
/// else (a signal, or no bytes at all) becomes `.fail("unknown")`.
pub fn forkCall(comptime Args: type, args: Args, comptime func: anytype, quote_wide: bool) !Outcome {
    return forkCallBufs(Args, args, func, quote_wide, null);
}

/// `forkCall` for a function that uses memory: after the result, the child also writes the
/// bytes of `bufs` as they are after the call, `,"bufs":["<hex>",…]` (two lowercase hex digits
/// per byte), and with `test_alloc` set the number of live allocations, `,"live":<n>`.
pub fn forkCallBufs(
    comptime Args: type,
    args: Args,
    comptime func: anytype,
    quote_wide: bool,
    bufs: ?[]const Buf,
) !Outcome {
    return forkCallBufsWithRenderingAllocator(Args, args, func, quote_wide, bufs, out_gpa);
}

/// Render only after the tested call returns. Keep the writer alive until its
/// complete byte sequence has been sent; any rendering error is a harness failure.
fn renderResult(
    raw: anytype,
    quote_wide: bool,
    bufs: ?[]const Buf,
    rendering_allocator: std.mem.Allocator,
    fd: std.posix.fd_t,
) !void {
    var aw: std.Io.Writer.Allocating = .init(rendering_allocator);
    defer aw.deinit();
    // One typed byte on the private pipe; it is removed from the legacy JSON payload.
    try aw.writer.writeByte(if (returnedError(@TypeOf(raw), raw)) 'E' else 'V');
    render_bufs = bufs orelse &.{};
    try renderPayload(@TypeOf(raw), &aw.writer, quote_wide, raw);
    if (bufs) |bs| {
        try aw.writer.writeAll(",\"bufs\":[");
        for (bs, 0..) |b, i| {
            if (i > 0) try aw.writer.writeAll(",");
            try aw.writer.writeAll("\"");
            for (b) |byte| try aw.writer.print("{x:0>2}", .{byte});
            try aw.writer.writeAll("\"");
        }
        try aw.writer.writeAll("]");
    }
    if (test_alloc) |ta| try aw.writer.print(",\"live\":{d}", .{ta.live.items.len});
    writeAll(fd, aw.written());
}

/// Test-runner injection point for the post-call renderer only. The tested function,
/// its allocator arguments and the parent's result storage are unchanged.
pub fn forkCallBufsWithRenderingAllocator(
    comptime Args: type,
    args: Args,
    comptime func: anytype,
    quote_wide: bool,
    bufs: ?[]const Buf,
    rendering_allocator: std.mem.Allocator,
) !Outcome {
    const fds = try compat.pipe();
    const pid = try compat.fork();
    if (pid == 0) {
        // Child: never returns. `panic_fd` lets `panic` above report a safety-check trip; the
        // stderr redirect below covers the unlikely case something still writes there (e.g. the
        // generic `panic.call` path) since that noise adds nothing over the `{"fail":...}` line
        // already recorded.
        compat.close(fds[0]);
        panic_fd = fds[1];
        compat.silenceStderr();
        // ReleaseSafe's inherited crash handler changes FPE/ILL/SEGV/BUS into ABRT.
        // Keep the original fault signal observable; the parent uses C/R for its phase.
        const crash_defaults = std.posix.Sigaction{
            .handler = .{ .handler = std.posix.SIG.DFL },
            .mask = std.posix.sigemptyset(),
            .flags = 0,
        };
        std.debug.updateSegfaultHandler(&crash_defaults);

        // Checked phase bytes distinguish a tested-call trap from renderer/protocol failure.
        if ((compat.write(fds[1], "C") catch reportHarnessFailure("harnessPhaseFailure")) != 1)
            reportHarnessFailure("harnessPhaseFailure");
        const raw = @call(.auto, func, args);
        if ((compat.write(fds[1], "R") catch reportHarnessFailure("harnessPhaseFailure")) != 1)
            reportHarnessFailure("harnessPhaseFailure");
        renderResult(raw, quote_wide, bufs, rendering_allocator, fds[1]) catch
            reportHarnessFailure("harnessRenderFailure");
        compat.exit(0);
    }

    // Parent.
    compat.close(fds[1]);
    var read_open = true;
    defer if (read_open) compat.close(fds[0]);
    var child_reaped = false;
    errdefer if (!child_reaped) {
        // Allocation errors must not leave a blocked tested call alive or unreaped.
        if (read_open) {
            compat.close(fds[0]);
            read_open = false;
        }
        std.posix.kill(pid, std.posix.SIG.KILL) catch {};
        _ = compat.waitpid(pid, 0);
    };
    var text: std.ArrayListUnmanaged(u8) = .empty;
    defer text.deinit(out_gpa);
    var chunk: [4096]u8 = undefined;
    var read_failed = false;
    while (true) {
        const n = std.posix.read(fds[0], &chunk) catch {
            read_failed = true;
            // A writer must not remain blocked on an undrained pipe while we wait.
            compat.close(fds[0]);
            read_open = false;
            break;
        };
        if (n == 0) break;
        try text.appendSlice(out_gpa, chunk[0..n]);
    }
    const wr = compat.waitpid(pid, 0);
    child_reaped = true;
    if (read_failed) return harnessFailure();
    // Only synchronous fault signals during the tested call are semantic observations.
    // Resource kills, cancellation and renderer-stage signals remain harness failures.
    if (std.posix.W.IFSIGNALED(wr.status) and std.mem.eql(u8, text.items, "C")) {
        const sig = std.posix.W.TERMSIG(wr.status);
        if (sig == std.posix.SIG.ILL or sig == std.posix.SIG.FPE or
            sig == std.posix.SIG.SEGV or sig == std.posix.SIG.BUS)
            return .{ .fail = .{ .name = try out_gpa.dupe(u8, "unknown"), .kind = .native_signal } };
    }
    if (text.items.len < 2 or text.items[0] != 'C') return harnessFailure();
    const returned = text.items[1] == 'R';
    const payload_start: usize = if (returned) 2 else 1;
    const payload = text.items[payload_start..];
    const exited_ok = std.posix.W.IFEXITED(wr.status) and std.posix.W.EXITSTATUS(wr.status) == 0;
    const exited_fail = std.posix.W.IFEXITED(wr.status) and std.posix.W.EXITSTATUS(wr.status) != 0;
    if (exited_fail and payload.len > 1 and (payload[0] == 'P' or payload[0] == 'H')) {
        const kind: OutcomeKind = if (!returned and payload[0] == 'P') .native_panic else .native_harness_failure;
        return .{ .fail = .{ .name = try out_gpa.dupe(u8, payload[1..]), .kind = kind } };
    }
    if (exited_ok and returned and payload.len > 1 and (payload[0] == 'V' or payload[0] == 'E')) {
        const kind: OutcomeKind = if (payload[0] == 'E') .error_return else .value;
        // Keep V/E for writeResult's existing payload[1..] protocol, without a second allocation.
        std.mem.copyForwards(u8, text.items, payload);
        text.items.len = payload.len;
        return .{ .ok = .{ .payload = try text.toOwnedSlice(out_gpa), .kind = kind } };
    }
    return harnessFailure();
}

pub fn writeResult(writer: anytype, outcome: Outcome) !void {
    switch (outcome) {
        .ok => |o| {
            defer out_gpa.free(o.payload);
            const payload = o.payload[1..];
            try writer.print("{{\"ok\":{s}}}\n", .{payload});
            if (metadata_writer) |meta| try meta.print(
                "{{\"schema\":1,\"kind\":\"{s}\",\"legacy\":{{\"ok\":{s}}}}}\n",
                .{ @tagName(o.kind), payload });
        },
        .fail => |f| {
            defer out_gpa.free(f.name);
            try writer.print("{{\"fail\":\"{s}\"}}\n", .{f.name});
            if (metadata_writer) |meta| try meta.print(
                "{{\"schema\":1,\"kind\":\"{s}\",\"legacy\":{{\"fail\":\"{s}\"}}}}\n",
                .{ @tagName(f.kind), f.name });
        },
    }
}

/// Re-exported so each tests/diff/<ex>/harness.zig calls `common.makePath` instead of importing
/// compat.zig itself.
pub const makePath = compat.makePath;
pub const fieldCount = compat.fieldCount;
pub const FieldType = compat.FieldType;

/// Reads `tests/diff/<ex>/inputs/<name>.jsonl`, opens `tests/diff/out/zig/<ex>/<name>.jsonl`,
/// and calls `perLine` for each non-empty input line with the parsed JSON array and the output
/// writer.
pub fn forEachLine(
    gpa: std.mem.Allocator,
    comptime ex: []const u8,
    comptime name: []const u8,
    perLine: anytype,
) !void {
    try forEachValue(gpa, ex, name, struct {
        fn call(a: std.mem.Allocator, v: std.json.Value, writer: anytype) !void {
            try perLine(a, v.array.items, writer);
        }
    }.call);
}

/// The loop of `forEachLine`: `perValue` gets each parsed line.
fn forEachValue(
    gpa: std.mem.Allocator,
    comptime ex: []const u8,
    comptime name: []const u8,
    perValue: anytype,
) !void {
    const in_path = "tests/diff/" ++ ex ++ "/inputs/" ++ name ++ ".jsonl";
    const out_path = "tests/diff/out/zig/" ++ ex ++ "/" ++ name ++ ".jsonl";

    const content = try compat.readFileAlloc(gpa, in_path, 4 << 20);
    defer gpa.free(content);
    var out_file = try compat.OutFile.open(out_path);
    defer out_file.close();
    const writer = out_file.writer();
    var metadata_file = try compat.OutFile.open(out_path ++ ".outcomes");
    defer metadata_file.close();
    const metadata = metadata_file.writer();
    metadata_writer = metadata;
    defer metadata_writer = null;

    var lines = std.mem.splitScalar(u8, content, '\n');
    while (lines.next()) |line| {
        if (line.len == 0) continue;
        var parsed = std.json.parseFromSlice(std.json.Value, gpa, line, .{}) catch |err| {
            try metadata.writeAll("{\"schema\":1,\"kind\":\"input_failure\"}\n");
            return err;
        };
        defer parsed.deinit();
        try perValue(gpa, parsed.value, writer);
    }
}


/// `forEachLine` for a function that uses memory: each input line is
/// `{"bufs":[[<byte>,…],…],"args":[…]}` (docs/generated-code.md §Differential test). `perLine`
/// gets the buffers (16-byte aligned copies of the bytes) and the args.
pub fn forEachMemLine(
    gpa: std.mem.Allocator,
    comptime ex: []const u8,
    comptime name: []const u8,
    perLine: anytype,
) !void {
    try forEachValue(gpa, ex, name, struct {
        fn call(a: std.mem.Allocator, v: std.json.Value, writer: anytype) !void {
            const bufsJ = v.object.get("bufs").?.array.items;
            const bufs = try a.alloc(Buf, bufsJ.len);
            defer a.free(bufs);
            for (bufsJ, bufs) |bj, *b| {
                b.* = try a.alignedAlloc(u8, comptime .fromByteUnits(16), bj.array.items.len);
                for (bj.array.items, b.*) |x, *byte| byte.* = @intCast(x.integer);
            }
            defer for (bufs) |b| a.free(b);
            try perLine(a, bufs, v.object.get("args").?.array.items, writer);
        }
    }.call);
}

/// A slice argument: `{"buf":<index>,"off":<offset>,"len":<items>}` into `bufs`, or `null` for
/// an optional slice type `S`.
pub fn sliceArg(comptime S: type, bufs: []const Buf, v: std.json.Value) S {
    if (v == .null) {
        if (@typeInfo(S) != .optional) unreachable;
        return null;
    }
    const T = switch (@typeInfo(S)) {
        .optional => |o| @typeInfo(o.child).pointer.child,
        else => @typeInfo(S).pointer.child,
    };
    const b = bufs[@intCast(v.object.get("buf").?.integer)];
    const items: [*]T = @ptrCast(@alignCast(b.ptr + @as(usize, @intCast(v.object.get("off").?.integer))));
    return items[0..@intCast(v.object.get("len").?.integer)];
}

/// A pointer argument: `{"buf":<index>,"off":<offset>}` into `bufs`, or `null` for an optional
/// pointer type `P`.
pub fn ptrArg(comptime P: type, bufs: []const Buf, v: std.json.Value) P {
    if (v == .null) {
        if (@typeInfo(P) != .optional) unreachable;
        return null;
    }
    const b = bufs[@intCast(v.object.get("buf").?.integer)];
    return @ptrCast(@alignCast(b.ptr + @as(usize, @intCast(v.object.get("off").?.integer))));
}
