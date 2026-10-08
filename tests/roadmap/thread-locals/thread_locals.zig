//! C02: thread-local storage (`docs/generated-code.md` §Thread-local storage). Every thread
//! has its own `counter`, initialized to 7 when the thread starts.

const std = @import("std");
const Thread = std.Thread;

threadlocal var counter: u32 = 7;

/// Increments this thread's own `counter` twice and reports the value it then reads.
fn bumpTwice(out: *u32) void {
    counter += 1;
    counter += 1;
    out.* = counter;
}

/// Two workers and the main thread increment their own `counter` concurrently. Each worker
/// reads 9 (7 + 2) and the main thread reads 8 (7 + 1), under every schedule, with no race.
pub fn twoCounters() !u32 {
    var a: u32 = 0;
    var b: u32 = 0;
    const h1 = try Thread.spawn(.{}, bumpTwice, .{&a});
    const h2 = try Thread.spawn(.{}, bumpTwice, .{&b});
    counter += 1;
    h1.join();
    h2.join();
    return a * 10000 + b * 100 + counter;
}

/// Hands the address of this thread's own `counter` to the caller.
fn leak(out: **u32) void {
    out.* = &counter;
}

/// Reads the worker's `counter` through the leaked pointer after the worker ended: the instance
/// died with its thread, so the read is a use after free.
pub fn leaked() !u32 {
    var p: *u32 = undefined;
    const h = try Thread.spawn(.{}, leak, .{&p});
    h.join();
    return p.*;
}

comptime {
    _ = &twoCounters;
    _ = &leaked;
}
