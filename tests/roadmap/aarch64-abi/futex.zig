//! T04 futex probe: the kernel's wait and wake calls that the OS rows of `ZigLean/Os/Futex.lean`
//! model (premises OSF-01, OSF-02), observed natively. `probe.zig` prints these rows after its
//! own; `tests/roadmap/aarch64-abi/Futex.lean` checks each one against the model's outcomes.
//!
//! Linux: `futex` with `FUTEX_WAIT`/`FUTEX_WAKE`, private and shared, through the std wrapper
//! that the translator binds (`futex_4arg`/`futex_3arg`; `futex_wait`/`futex_wake` on 0.14.1)
//! wherever its pointer type can carry the address, else through the raw system call. macOS:
//! libc's `__ulock_wait2`, `__ulock_wait` and `__ulock_wake` with `COMPARE_AND_WAIT | NO_ERRNO`.
//!
//! A row is `futex <case> <value>`. A value is a return code as a signed decimal (`-errno` on
//! failure), or a list of them. Every row is the same on every run: a threaded case records only
//! what does not depend on when its waiters fall asleep (the waker repeats its call until every
//! waiter has returned, and a case with several waiters records the returns only where each one
//! is forced). A case that does not finish within its bound prints `stuck`.
const std = @import("std");
const builtin = @import("builtin");

const is_linux = builtin.os.tag == .linux;
const linux = std.os.linux;
const c = std.c;
/// 0.15.0 on: `futex_4arg`/`futex_3arg` with an `anyopaque` address and a `FUTEX_OP`.
const v15 = builtin.zig_version.minor >= 15;

const Timespec = extern struct { sec: isize, nsec: isize };

const WAIT: u32 = 0;
const WAKE: u32 = 1;
const PRIVATE: u32 = 0x80;
const EINTR: isize = -4;
const ENOENT: isize = -2;

/// Linux `futex(addr, op, val, timeout)` for `FUTEX_WAIT` (four arguments) or `FUTEX_WAKE` (three).
fn futex(addr: usize, op: u32, val: u32, timeout: ?*const Timespec) isize {
    const wait = op & ~PRIVATE == WAIT;
    const ts: ?*const linux.timespec = @ptrCast(timeout);
    // A non-optional pointer cannot be null, and 0.14.1's `*const i32` cannot be unaligned.
    const raw = addr == 0 or (!v15 and addr % 4 != 0);
    const r: usize = if (raw)
        (if (wait) linux.syscall4(.futex, addr, op, val, @intFromPtr(timeout)) else linux.syscall3(.futex, addr, op, val))
    else if (v15)
        (if (wait) linux.futex_4arg(@ptrFromInt(addr), @bitCast(op), val, ts) else linux.futex_3arg(@ptrFromInt(addr), @bitCast(op), val))
    else if (wait)
        linux.futex_wait(@ptrFromInt(addr), op, @bitCast(val), ts)
    else
        linux.futex_wake(@ptrFromInt(addr), op, @bitCast(val));
    return @bitCast(r);
}

fn ul(wake_all: bool) c.UL {
    return .{ .op = .COMPARE_AND_WAIT, .WAKE_ALL = wake_all, .NO_ERRNO = true };
}

/// macOS wait: `__ulock_wait2` (nanoseconds) or the older `__ulock_wait` (microseconds); a
/// timeout of 0 waits without one.
fn ulockWait(old: bool, addr: usize, val: u32, timeout: u32) isize {
    const p: ?*const anyopaque = @ptrFromInt(addr);
    return if (old) c.__ulock_wait(ul(false), p, val, timeout) else c.__ulock_wait2(ul(false), p, val, timeout, 0);
}

fn ulockWake(addr: usize, wake_all: bool) isize {
    return c.__ulock_wake(ul(wake_all), @ptrFromInt(addr), 0);
}

/// Sleeps for about `us` microseconds: a timed wait at a word of its own that nobody wakes.
fn nap(us: u32) void {
    var word: u32 = 0;
    if (is_linux) {
        const ts: Timespec = .{ .sec = 0, .nsec = @as(isize, us) * 1000 };
        _ = futex(@intFromPtr(&word), WAIT | PRIVATE, 0, &ts);
    } else {
        _ = ulockWait(false, @intFromPtr(&word), 0, us * 1000);
    }
}

/// How a waiter waits: Linux's domain and macOS's call, and whether with a (long) timeout.
const How = struct { shared: bool = false, old: bool = false, timed: bool = false };

const max_waiters = 3;

/// The waiters of one case. The word stays 0, so a wait ends only by a wake (or `EINTR`, which
/// is retried). The struct lives on the main thread's stack: anonymous memory, as a shared
/// Linux key needs it (`Mem.anonAt`).
const Waiters = struct {
    word: u32 = 0,
    done: u32 = 0,
    codes: [max_waiters]isize = @splat(0),
    threads: [max_waiters]std.Thread = undefined,
    n: usize = 0,

    fn wait(self: *Waiters, i: usize, how: How) void {
        const addr = @intFromPtr(&self.word);
        const long: Timespec = .{ .sec = 60, .nsec = 0 };
        var r: isize = EINTR;
        while (r == EINTR) {
            r = if (is_linux)
                futex(addr, if (how.shared) WAIT else WAIT | PRIVATE, 0, if (how.timed) &long else null)
            else
                ulockWait(how.old, addr, 0, if (!how.timed) 0 else if (how.old) 60_000_000 else std.math.maxInt(u32));
        }
        self.codes[i] = r;
        _ = @atomicRmw(u32, &self.done, .Add, 1, .seq_cst);
    }

    fn start(self: *Waiters, n: usize, how: How) !void {
        self.n = n;
        for (0..n) |i| self.threads[i] = try std.Thread.spawn(.{}, wait, .{ self, i, how });
    }

    fn finished(self: *Waiters) usize {
        return @atomicLoad(u32, &self.done, .seq_cst);
    }

    fn join(self: *Waiters) void {
        for (self.threads[0..self.n]) |t| t.join();
    }
};

/// The bound of a threaded case: this many 200 µs naps (10 s).
const patience = 50_000;

/// A list of return codes, printed as `a,b,c` (`-` if empty).
const Codes = struct {
    items: [8]isize = undefined,
    len: usize = 0,
    stuck: bool = false,

    fn add(self: *Codes, r: isize) void {
        if (self.len == self.items.len) {
            self.stuck = true;
            return;
        }
        self.items[self.len] = r;
        self.len += 1;
    }

    fn print(self: *const Codes, out: anytype) !void {
        if (self.stuck) return out.print("stuck", .{});
        if (self.len == 0) return out.print("-", .{});
        for (self.items[0..self.len], 0..) |r, i| try out.print("{s}{d}", .{ if (i == 0) "" else ",", r });
    }
};

fn codesOf(w: *const Waiters) Codes {
    var codes: Codes = .{};
    for (w.codes[0..w.n]) |r| codes.add(r);
    return codes;
}

/// Linux: `n` waiters in `how`'s domain; the waker repeats `FUTEX_WAKE` with `val` in the domain
/// `wake_shared` until every waiter has returned. The result is the calls' non-zero returns, in
/// order.
fn linuxWake(w: *Waiters, n: usize, how: How, wake_shared: bool, val: u32) !Codes {
    var rets: Codes = .{};
    try w.start(n, how);
    var naps: u32 = 0;
    while (w.finished() < n and !rets.stuck) {
        const r = futex(@intFromPtr(&w.word), if (wake_shared) WAKE else WAKE | PRIVATE, val, null);
        if (r != 0) {
            rets.add(r);
            continue;
        }
        nap(200);
        naps += 1;
        if (naps == patience) rets.stuck = true;
    }
    // A stuck case leaves its waiters asleep: wake them, whatever the case's own call does.
    while (w.finished() < n) : (nap(200)) _ = futex(@intFromPtr(&w.word), if (how.shared) WAKE else WAKE | PRIVATE, max_waiters, null);
    w.join();
    return rets;
}

fn linuxRows(out: anytype) !void {
    var word: u32 = 1;
    const at = @intFromPtr(&word);
    // Bits 63 and 55 set: an address that no `access_ok` admits (`Linux.futexKey`).
    const kernel: usize = (1 << 63) | (1 << 55);
    const ms: Timespec = .{ .sec = 0, .nsec = 1_000_000 };
    const zero: Timespec = .{ .sec = 0, .nsec = 0 };
    const bad_nsec: Timespec = .{ .sec = 0, .nsec = 1_000_000_000 };
    const neg_nsec: Timespec = .{ .sec = 0, .nsec = -1 };
    const neg_sec: Timespec = .{ .sec = -1, .nsec = 0 };

    inline for (.{ "private", "shared" }) |domain| {
        const flag: u32 = if (comptime std.mem.eql(u8, domain, "private")) PRIVATE else 0;
        const wait = WAIT | flag;
        const wake = WAKE | flag;
        // WAIT: the word is 1. An expected value of 0 is a mismatch; 1 sleeps.
        try out.print("futex wait_{s}_mismatch {d}\n", .{ domain, futex(at, wait, 0, null) });
        try out.print("futex wait_{s}_mismatch_timed {d}\n", .{ domain, futex(at, wait, 0, &ms) });
        try out.print("futex wait_{s}_timeout {d}\n", .{ domain, futex(at, wait, 1, &ms) });
        try out.print("futex wait_{s}_timeout_zero {d}\n", .{ domain, futex(at, wait, 1, &zero) });
        try out.print("futex wait_{s}_bad_nsec {d}\n", .{ domain, futex(at, wait, 1, &bad_nsec) });
        try out.print("futex wait_{s}_neg_nsec {d}\n", .{ domain, futex(at, wait, 1, &neg_nsec) });
        try out.print("futex wait_{s}_neg_sec {d}\n", .{ domain, futex(at, wait, 1, &neg_sec) });
        // The order of the checks: timeout, alignment, address, word.
        try out.print("futex wait_{s}_bad_nsec_mismatch {d}\n", .{ domain, futex(at, wait, 0, &bad_nsec) });
        try out.print("futex wait_{s}_bad_nsec_unaligned {d}\n", .{ domain, futex(at + 1, wait, 1, &bad_nsec) });
        try out.print("futex wait_{s}_bad_nsec_kernel {d}\n", .{ domain, futex(kernel, wait, 1, &bad_nsec) });
        try out.print("futex wait_{s}_unaligned {d}\n", .{ domain, futex(at + 1, wait, 1, null) });
        try out.print("futex wait_{s}_unaligned2 {d}\n", .{ domain, futex(at + 2, wait, 1, null) });
        try out.print("futex wait_{s}_unaligned_kernel {d}\n", .{ domain, futex(kernel + 1, wait, 1, null) });
        try out.print("futex wait_{s}_kernel {d}\n", .{ domain, futex(kernel, wait, 1, null) });
        try out.print("futex wait_{s}_kernel_top {d}\n", .{ domain, futex(std.math.maxInt(usize) - 3, wait, 1, null) });
        try out.print("futex wait_{s}_null {d}\n", .{ domain, futex(0, wait, 1, null) });
        // WAKE with nobody waiting.
        try out.print("futex wake_{s}_none {d}\n", .{ domain, futex(at, wake, 1, null) });
        try out.print("futex wake_{s}_none_val0 {d}\n", .{ domain, futex(at, wake, 0, null) });
        try out.print("futex wake_{s}_none_max {d}\n", .{ domain, futex(at, wake, std.math.maxInt(i32), null) });
        try out.print("futex wake_{s}_unaligned {d}\n", .{ domain, futex(at + 1, wake, 1, null) });
        try out.print("futex wake_{s}_unaligned_kernel {d}\n", .{ domain, futex(kernel + 1, wake, 1, null) });
        try out.print("futex wake_{s}_kernel {d}\n", .{ domain, futex(kernel, wake, 1, null) });
        try out.print("futex wake_{s}_kernel_top {d}\n", .{ domain, futex(std.math.maxInt(usize) - 3, wake, 1, null) });
        try out.print("futex wake_{s}_null {d}\n", .{ domain, futex(0, wake, 1, null) });
    }

    // One waiter: the first non-zero return of the wake, and the waiter's return. `val` is an
    // `int` in the kernel: 0 and 0xffffffff (-1) still wake one (`Linux.wakeLimit`).
    inline for (.{
        .{ "private", How{}, false },
        .{ "shared", How{ .shared = true }, true },
        .{ "private_timed", How{ .timed = true }, false },
    }) |case| {
        inline for (.{ 1, 2, 0, 0x7fffffff, 0xffffffff }) |val| {
            var w: Waiters = .{};
            const rets = try linuxWake(&w, 1, case[1], case[2], val);
            try out.print("futex wake1_{s}_val{x} ", .{ case[0], val });
            try rets.print(out);
            try out.print("/{d}\n", .{w.codes[0]});
        }
    }
    // Three waiters and a wake limit of one: three non-zero returns, each 1.
    inline for (.{ 1, 0, 0xffffffff }) |val| {
        var w: Waiters = .{};
        const rets = try linuxWake(&w, 3, .{}, false, val);
        try out.print("futex wake3_private_val{x} ", .{val});
        try rets.print(out);
        try out.print("/", .{});
        try codesOf(&w).print(out);
        try out.print("\n", .{});
    }
    // Three waiters and a larger limit: how the returns split depends on when the waiters fall
    // asleep, so the row has their sum and the number of returns above the limit.
    inline for (.{ 2, 0x7fffffff }) |val| {
        var w: Waiters = .{};
        const rets = try linuxWake(&w, 3, .{}, false, val);
        var sum: isize = 0;
        var above: usize = 0;
        for (rets.items[0..rets.len]) |r| {
            sum += r;
            if (r > val) above += 1;
        }
        if (rets.stuck) try out.print("futex wake3_private_val{x} stuck\n", .{val}) else {
            try out.print("futex wake3_private_val{x} sum={d},above={d}/", .{ val, sum, above });
            try codesOf(&w).print(out);
            try out.print("\n", .{});
        }
    }
    // The two domains have different keys at one address: a wake in the other domain wakes
    // nobody, also once the waiter sleeps (20 ms later); a wake in the waiter's domain wakes it.
    inline for (.{ .{ "shared", true }, .{ "private", false } }) |case| {
        var w: Waiters = .{};
        try w.start(1, .{ .shared = case[1] });
        nap(20_000);
        const other = futex(@intFromPtr(&w.word), if (case[1]) WAKE | PRIVATE else WAKE, std.math.maxInt(i32), null);
        var own: isize = 0;
        var naps: u32 = 0;
        while (own == 0 and naps < patience) : (naps += 1) {
            own = futex(@intFromPtr(&w.word), if (case[1]) WAKE else WAKE | PRIVATE, 1, null);
            if (own == 0) nap(200);
        }
        w.join();
        try out.print("futex domain_{s}_waiter {d},{d}/{d}\n", .{ case[0], other, own, w.codes[0] });
    }
}

/// macOS: `n` waiters; the waker repeats `__ulock_wake` until every waiter has returned, and
/// after each successful wake waits for a waiter to return (a second wake before that may find
/// the key's `ull` alive and return 0 without waking anybody). The result is the calls' returns
/// other than `-ENOENT` (nobody asleep yet), in order; with `distinct`, each value once.
fn macosWake(w: *Waiters, n: usize, how: How, wake_all: bool, distinct: bool) !Codes {
    var rets: Codes = .{};
    try w.start(n, how);
    var naps: u32 = 0;
    while (w.finished() < n and !rets.stuck) {
        const before = w.finished();
        const r = ulockWake(@intFromPtr(&w.word), wake_all);
        if (r != ENOENT and !(distinct and std.mem.indexOfScalar(isize, rets.items[0..rets.len], r) != null)) rets.add(r);
        if (r == 0) {
            while (w.finished() == before and naps < patience) : (naps += 1) nap(200);
        } else {
            nap(200);
            naps += 1;
        }
        if (naps >= patience) rets.stuck = true;
    }
    while (w.finished() < n) : (nap(200)) _ = ulockWake(@intFromPtr(&w.word), true);
    w.join();
    return rets;
}

fn macosRows(out: anytype) !void {
    var word: u32 = 1;
    const at = @intFromPtr(&word);
    // An aligned address in the unmapped zero page.
    const unmapped: usize = 8;

    inline for (.{ .{ "wait2", false, 1_000_000 }, .{ "wait", true, 1000 } }) |call| {
        const old = call[1];
        // The word is 1. An expected value of 0 is a mismatch; 1 sleeps (for 1 ms).
        try out.print("futex {s}_mismatch {d}\n", .{ call[0], ulockWait(old, at, 0, 0) });
        try out.print("futex {s}_mismatch_timed {d}\n", .{ call[0], ulockWait(old, at, 0, call[2]) });
        try out.print("futex {s}_timeout {d}\n", .{ call[0], ulockWait(old, at, 1, call[2]) });
        try out.print("futex {s}_null {d}\n", .{ call[0], ulockWait(old, 0, 1, 0) });
        try out.print("futex {s}_null_timed {d}\n", .{ call[0], ulockWait(old, 0, 1, call[2]) });
        try out.print("futex {s}_unaligned {d}\n", .{ call[0], ulockWait(old, at + 1, 1, 0) });
        try out.print("futex {s}_unaligned2 {d}\n", .{ call[0], ulockWait(old, at + 2, 0, 0) });
        try out.print("futex {s}_unmapped {d}\n", .{ call[0], ulockWait(old, unmapped, 1, 0) });
    }
    inline for (.{ .{ "one", false }, .{ "all", true } }) |call| {
        try out.print("futex wake_{s}_none {d}\n", .{ call[0], ulockWake(at, call[1]) });
        try out.print("futex wake_{s}_null {d}\n", .{ call[0], ulockWake(0, call[1]) });
        try out.print("futex wake_{s}_unaligned {d}\n", .{ call[0], ulockWake(at + 1, call[1]) });
        try out.print("futex wake_{s}_unmapped {d}\n", .{ call[0], ulockWake(unmapped, call[1]) });
    }

    // One waiter: the wake's returns until it has returned (one success, 0), and its return
    // (`--ull_nwaiters`: nobody else waits).
    inline for (.{
        .{ "wait2", How{} },
        .{ "wait", How{ .old = true } },
        .{ "wait2_timed", How{ .timed = true } },
        .{ "wait_timed", How{ .old = true, .timed = true } },
    }) |waiter| {
        inline for (.{ .{ "one", false }, .{ "all", true } }) |call| {
            var w: Waiters = .{};
            const rets = try macosWake(&w, 1, waiter[1], call[1], false);
            try out.print("futex wake1_{s}_{s} ", .{ call[0], waiter[0] });
            try rets.print(out);
            try out.print("/{d}\n", .{w.codes[0]});
        }
    }
    // Three waiters. A wake of one wakes exactly one: three successes. `WAKE_ALL` wakes every
    // waiter asleep at that moment, so the row has its distinct returns. A waiter returns the
    // number of waiters still in the kernel at its key, which depends on when the others fell
    // asleep: the row has `n` for a non-negative return.
    inline for (.{ .{ "one", false }, .{ "all", true } }) |call| {
        var w: Waiters = .{};
        const rets = try macosWake(&w, 3, .{}, call[1], call[1]);
        try out.print("futex wake3_{s} ", .{call[0]});
        try rets.print(out);
        for (w.codes[0..w.n], 0..) |r, i| {
            try out.print("{s}", .{if (i == 0) "/" else ","});
            if (r >= 0) try out.print("n", .{}) else try out.print("{d}", .{r});
        }
        try out.print("\n", .{});
    }
}

/// A lock built on the probed calls alone (Drepper's three-state mutex: 0 free, 1 held, 2 held
/// with waiters), around a plain counter.
const Lock = struct {
    state: u32 = 0,
    counter: u64 = 0,

    fn sleep(self: *Lock) void {
        const addr = @intFromPtr(&self.state);
        _ = if (is_linux) futex(addr, WAIT | PRIVATE, 2, null) else ulockWait(false, addr, 2, 0);
    }

    fn lock(self: *Lock) void {
        if (@cmpxchgStrong(u32, &self.state, 0, 1, .acquire, .monotonic) == null) return;
        while (@atomicRmw(u32, &self.state, .Xchg, 2, .acquire) != 0) self.sleep();
    }

    fn unlock(self: *Lock) void {
        if (@atomicRmw(u32, &self.state, .Xchg, 0, .release) != 2) return;
        const addr = @intFromPtr(&self.state);
        _ = if (is_linux) futex(addr, WAKE | PRIVATE, 1, null) else ulockWake(addr, false);
    }

    fn work(self: *Lock, rounds: usize) void {
        for (0..rounds) |_| {
            self.lock();
            self.counter += 1;
            self.unlock();
        }
    }
};

/// `futex mutex <threads>x<rounds>=<counter>`: no increment is lost (mutual exclusion) and the
/// run ends (no wake is lost).
fn mutexRow(out: anytype) !void {
    const rounds = 20_000;
    var lock: Lock = .{};
    var threads: [4]std.Thread = undefined;
    for (&threads) |*t| t.* = try std.Thread.spawn(.{}, Lock.work, .{ &lock, rounds });
    for (threads) |t| t.join();
    try out.print("futex mutex {d}x{d}={d}\n", .{ threads.len, rounds, lock.counter });
}

pub fn rows(out: anytype) !void {
    if (is_linux) try linuxRows(out) else try macosRows(out);
    try mutexRow(out);
}
