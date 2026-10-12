//! L14: error return tracing (`-ferror-tracing`). The exporter writes the trace operations and
//! the hidden trace parameter (`docs/air-json.md` §Error return trace); the translator makes the
//! trace data flow (`Canon.errTraces`) and the trace's memory ordinary model memory, so the
//! recorded index is observable and compared natively (`check.sh`).
const std = @import("std");

const E = error{ Bad, Worse };
pub const Big = struct { a: [6]u64 };

/// A large error union is built in the result pointer and returned with `ret_load`: under error
/// tracing Sema checks it with `is_non_err_ptr` before `returnError` (Zig 0.14.1, 0.15.2, 0.17.0).
pub noinline fn bigRet(x: u64) E!Big {
    if (x == 0) return error.Bad;
    if (x == 1) return error.Worse;
    return .{ .a = .{ x, x, x, x, x, x } };
}

/// `try` records the propagated error (`returnError`) and passes the trace on.
pub noinline fn pass(x: u64) E!u64 {
    const b = try bigRet(x);
    return b.a[5] + 1;
}

/// The number of error returns recorded so far in the current trace.
pub noinline fn traceIndex() usize {
    const t = @errorReturnTrace() orelse return 99;
    return t.index;
}

/// The trace index seen inside the error branch, or the payload: the trace (and so the index)
/// is per root call, set up by this C-callable function.
export fn traced(x: u64) u64 {
    if (pass(x)) |v| return v else |e| return @as(u64, if (e == error.Bad) 1000 else 2000) + traceIndex();
}

/// A handled error restores the trace index (`save_err_return_trace_index`), so a later error is
/// recorded from the same index again.
export fn handledTwice(x: u64) u64 {
    const a = pass(x) catch 7;
    const before = traceIndex();
    const b = pass(x) catch 9;
    return a + b + 100 * before + 10000 * traceIndex();
}

pub fn main() void {
    for ([_]u64{ 0, 1, 5 }) |x| {
        std.debug.print("traced {d} {d}\n", .{ x, traced(x) });
        std.debug.print("handledTwice {d} {d}\n", .{ x, handledTwice(x) });
    }
}
