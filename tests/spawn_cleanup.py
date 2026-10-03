#!/usr/bin/env python3
"""Fail the second task launch deterministically at the std boundary.

Copies the actual examples into a temporary directory and substitutes only their
Thread/Io imports. Successful tasks remain pending until join/cancel, so missing
error cleanup is observable without exhausting OS resources or racing stack reuse.
Run: python3 tests/spawn_cleanup.py /path/to/stock/zig
"""
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
ZIG = sys.argv[1] if len(sys.argv) > 1 else "zig"
VERSION = subprocess.check_output([ZIG, "version"], text=True).strip()

THREAD_MOCK = r'''
const std = @import("std");
pub var spawned: usize = 0;
pub var joined: usize = 0;
pub var fail_at: usize = 2;
pub fn reset() void { spawned = 0; joined = 0; fail_at = 2; }
pub const Thread = struct {
    context: *anyopaque,
    run: *const fn (*anyopaque) void,
    pub const Mutex = std.Thread.Mutex;
    pub const Condition = std.Thread.Condition;
    pub const ResetEvent = std.Thread.ResetEvent;
    pub const WaitGroup = std.Thread.WaitGroup;
    pub fn spawn(_: anytype, comptime function: anytype, args: anytype) error{ThreadQuotaExceeded}!Thread {
        spawned += 1;
        if (spawned == fail_at) return error.ThreadQuotaExceeded;
        const Context = @TypeOf(args[0]);
        const Runner = struct {
            fn run(ptr: *anyopaque) void { function(@as(Context, @ptrCast(@alignCast(ptr)))); }
        };
        return .{ .context = args[0], .run = Runner.run };
    }
    pub fn join(self: Thread) void { self.run(self.context); joined += 1; }
};
'''

GROUP_MOCK = r'''
pub var submitted: usize = 0;
pub var canceled: usize = 0;
pub fn reset() void { submitted = 0; canceled = 0; }
pub const Io = struct {
    pub const Mutex = struct {
        pub const init: Mutex = .{};
        pub fn lockUncancelable(_: *Mutex, _: Io) void {}
        pub fn unlock(_: *Mutex, _: Io) void {}
    };
    pub const Group = struct {
        context: ?*anyopaque = null,
        run: ?*const fn (*anyopaque) void = null,
        pub const init: Group = .{};
        fn submit(self: *Group, comptime function: anytype, args: anytype) void {
            const Context = @TypeOf(args[0]);
            const Runner = struct {
                fn run(ptr: *anyopaque) void { function(@as(Context, @ptrCast(@alignCast(ptr)))); }
            };
            self.context = args[0]; self.run = Runner.run;
        }
        pub fn async(self: *Group, _: Io, comptime function: anytype, args: anytype) void {
            self.submit(function, args);
        }
        pub fn concurrent(self: *Group, _: Io, comptime function: anytype, args: anytype) error{ConcurrencyUnavailable}!void {
            submitted += 1;
            if (submitted == 2) return error.ConcurrencyUnavailable;
            self.submit(function, args);
        }
        pub fn await(self: *Group, io: Io) error{Canceled}!void { self.cancel(io); }
        pub fn cancel(self: *Group, _: Io) void {
            if (self.context) |ptr| { self.run.?(ptr); self.context = null; canceled += 1; }
        }
    };
};
'''

CASES = {
    "threads": ["parallelCounter(3)", "race(9, 10)", "disjoint(9, 10)", "xchgRace(9, 10)", "claimOnce()"],
    "atomics": ["sbRelaxed()", "twoPlusTwoW()", "stackPush()"],
    "threadsync": ["waitGroup()"],
    "iogroup": ["groupConcurrent(.{})"],
}

with tempfile.TemporaryDirectory(prefix="air2lean-spawn-cleanup-") as temporary:
    directory = pathlib.Path(temporary)
    for example, calls in CASES.items():
        if example == "threadsync" and VERSION != "0.15.2":
            continue
        if example == "iogroup" and VERSION != "0.16.0":
            continue
        source = (ROOT / "examples" / example / (example + ".zig")).read_text()
        group = example == "iogroup"
        source = source.replace('const Io = std.Io;', 'const Io = @import("fault").Io;') if group else source.replace('const Thread = std.Thread;', 'const Thread = @import("fault").Thread;')
        (directory / "example.zig").write_text(source)
        (directory / "fault.zig").write_text(GROUP_MOCK if group else THREAD_MOCK)
        error = "ConcurrencyUnavailable" if group else "ThreadQuotaExceeded"
        counter = "canceled" if group else "joined"
        tests = 'const std = @import("std"); const ex = @import("ex"); const fault = @import("fault");\n'
        for call in calls:
            failures = [2, 3, 4] if call.startswith("parallelCounter") else [2]
            for failure in failures:
                configure = f"fault.fail_at = {failure};" if not group else ""
                tests += f'test "{call} cleans up failed launch {failure}" {{ fault.reset(); {configure} try std.testing.expectError(error.{error}, ex.{call}); try std.testing.expectEqual(@as(usize, {failure - 1}), fault.{counter}); }}\n'
        (directory / "tests.zig").write_text(tests)
        subprocess.run([ZIG, "test", "-OReleaseSafe", "--cache-dir", str(directory / "cache"), "--global-cache-dir", str(directory / "global"), "--dep", "ex", "--dep", "fault", "-Mroot=" + str(directory / "tests.zig"), "--dep", "fault", "-Mex=" + str(directory / "example.zig"), "-Mfault=" + str(directory / "fault.zig")], check=True, cwd=ROOT)
