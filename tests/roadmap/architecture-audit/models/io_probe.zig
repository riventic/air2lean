//! Architecture audit (models, area 5): `std.Io` model divergences (Zig 0.16.0).
//! `std.Io` is collapsed to the model's `Zig.Io` (`Ty.io`); `Io.Group.cancel` is modelled as
//! `Io.Group.await` and the cancelable `Io.futexWait` never returns `error.Canceled`
//! (`Air2Lean/StdModels.lean`, `docs/std-models.md` §Io.Group).
const std = @import("std");
const Io = std.Io;

const Box = struct {
    word: u32 = 0,
    out: u32 = 0,
};

fn waiter(io: Io, b: *Box) void {
    // Nobody ever wakes `word`: only cancelation (or a spurious wakeup) ends this wait.
    io.futexWait(u32, &b.word, 0) catch {
        b.out = 1;
        return;
    };
    b.out = 2;
}

/// D-IO-CANCEL: native `std.Io.Threaded` delivers the cancelation request to the waiting
/// task, whose futexWait returns error.Canceled: result 1. The model's `cancel` is `await`
/// and its futexWait never cancels, so the task waits forever: every schedule ends in
/// `Zig.Error.deadlock` (no result 1 exists in the model).
pub fn cancelProbe(io: Io) u32 {
    var b: Box = .{};
    var g: Io.Group = .init;
    g.async(io, waiter, .{ io, &b });
    g.cancel(io);
    return b.out;
}

fn handoffWaiter(io: Io, b: *Box) void {
    while (@atomicLoad(u32, &b.word, .acquire) == 0) io.futexWaitUncancelable(u32, &b.word, 0);
    b.out = 5;
}

/// D-IO-INLINE: under the default `available` spawn policy (THR-02) every `Group.async` task
/// is a new model thread, so this hand-off returns 5 on every schedule. `std.Io` is one model
/// type whatever implementation the caller passes; with `std.Io.Threaded.global_single_threaded`
/// (or any Io that runs `async` inline, as the API permits) the task runs inside `async`,
/// waits for a store that comes after `async` returns, and the program hangs.
pub fn handoffProbe(io: Io) u32 {
    var b: Box = .{};
    var g: Io.Group = .init;
    g.async(io, handoffWaiter, .{ io, &b });
    @atomicStore(u32, &b.word, 1, .release);
    io.futexWake(u32, &b.word, 1);
    g.await(io) catch return 0;
    return b.out;
}

comptime {
    _ = &cancelProbe;
    _ = &handoffProbe;
}
