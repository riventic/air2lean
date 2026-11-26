//! Opaque types that the standard library declares (check.sh): a pointer to one can be the
//! handle of a hand-written std model, so the translator rejects every use of it.
const std = @import("std");
const Io = std.Io;

fn square(x: u32) u32 {
    return x *% x;
}

// `Io.Future.any_future: ?*Io.AnyFuture` is the model's runtime record (`Zig.Future`). Its
// first word is the model's thread id; natively it is the first word of the implementation's
// future.
pub fn peek(io: Io, x: u32) u64 {
    var f = io.async(square, .{x});
    const w = @as(*u64, @ptrCast(@alignCast(f.any_future.?))).*;
    _ = f.await(io);
    return w;
}

// Natively `null` when the task ran inline; the model always has its record.
pub fn pending(io: Io, x: u32) bool {
    var f = io.async(square, .{x});
    const p = f.any_future != null;
    _ = f.await(io);
    return p;
}

// The handle type alone, outside the modelled `Io.Future`.
pub noinline fn isNull(h: ?*Io.AnyFuture) bool {
    return h == null;
}

comptime {
    _ = &peek;
    _ = &pending;
    _ = &isNull;
}
