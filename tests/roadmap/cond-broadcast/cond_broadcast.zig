//! C14: std's condition broadcast, for every supported Zig version. 0.16.0 and 0.17.1 have
//! `Io.Condition.broadcast`; 0.14.1 and 0.15.2 have `Thread.Condition.broadcast`
//! (`FutexImpl.wake(.all)`). The fixture exports each version's broadcast (exports.json);
//! check.sh translates it and requires the translation of the code the condition contract's
//! implementations prove (`CondImpl.broadcast_wp`: `Proofs/Sync/Cond.lean`,
//! `Proofs/Threadsync/Cond.lean`).

const std = @import("std");
const builtin = @import("builtin");

comptime {
    if (builtin.zig_version.minor >= 16) {
        _ = &std.Io.Condition.broadcast;
    } else {
        _ = &std.Thread.Condition.broadcast;
    }
}
