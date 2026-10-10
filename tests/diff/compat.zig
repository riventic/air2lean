//! Version compat shim for Zig 0.15.2 vs 0.16.0 (and 0.17.0's type reflection, at the end) —
//! the only file in tests/diff/ and
//! tests/floatprobe/ with a Zig-version or OS switch; every other file there imports this and
//! stays version-agnostic. 0.16.0 removed std.posix's process layer (fork/pipe/write/waitpid/
//! dup2/exit/abort/close — `read` and `std.posix.{W,errno,system,fd_t,STDERR_FILENO}` are
//! unchanged and used directly by callers), replaced std.fs.{Dir,File,cwd()} with
//! std.Io.{Dir,File} plus an explicit `Io` execution context, and renamed
//! std.heap.GeneralPurposeAllocator to DebugAllocator (an unconditional rename, handled at each
//! call site instead of here).
//!
//! macOS + Linux only (this project's two targets) — no wasi/windows paths.
//!
//! Imported directly (same directory) by common.zig and gen_inputs.zig; wired in as the
//! `compat` module for tests/floatprobe/probe.zig (scripts/floatprobe.sh), which lives
//! elsewhere.

const std = @import("std");
const builtin = @import("builtin");
const is_linux = builtin.os.tag == .linux;
const posix = std.posix;
const system = posix.system;

/// True from 0.16.0 onward. Comptime-known, so `if (v16) ... else ...` below only ever
/// semantically analyzes the branch that applies to the Zig compiling this file.
const v16 = builtin.zig_version.minor >= 16;

/// 0.16.0's file/dir ops take an explicit `Io` execution context instead of always running
/// synchronously on the calling thread; this project has no async runtime, so every call site
/// uses the same single-threaded one.
fn ioCtx() std.Io {
    return std.Io.Threaded.global_single_threaded.io();
}

// -- process layer (tests/diff/common.zig's forkCall/reportPanic) ---------------------------

pub fn pipe() ![2]posix.fd_t {
    if (!v16) return posix.pipe();
    var fds: [2]posix.fd_t = undefined;
    return switch (posix.errno(system.pipe(&fds))) {
        .SUCCESS => fds,
        else => error.SystemResources,
    };
}

pub fn fork() !posix.pid_t {
    if (!v16) return posix.fork();
    const rc = system.fork();
    return switch (posix.errno(rc)) {
        .SUCCESS => @intCast(rc),
        else => error.SystemResources,
    };
}

pub fn close(fd: posix.fd_t) void {
    if (!v16) return posix.close(fd);
    _ = system.close(fd);
}

pub fn dup2(old_fd: posix.fd_t, new_fd: posix.fd_t) !void {
    if (!v16) return posix.dup2(old_fd, new_fd);
    while (true) {
        switch (posix.errno(system.dup2(old_fd, new_fd))) {
            .SUCCESS => return,
            .INTR => continue,
            else => return error.Unexpected,
        }
    }
}

pub fn write(fd: posix.fd_t, bytes: []const u8) !usize {
    if (!v16) return posix.write(fd, bytes);
    if (bytes.len == 0) return 0;
    while (true) {
        const rc = system.write(fd, bytes.ptr, bytes.len);
        switch (posix.errno(rc)) {
            .SUCCESS => return @intCast(rc),
            .INTR => continue,
            else => return error.Unexpected,
        }
    }
}

pub const WaitPidResult = struct { pid: posix.pid_t, status: u32 };

pub fn waitpid(pid: posix.pid_t, flags: u32) WaitPidResult {
    if (!v16) {
        const r = posix.waitpid(pid, flags);
        return .{ .pid = r.pid, .status = r.status };
    }
    // The status pointee of this std's waitpid: c_int with libc; on Linux u32 (0.16.0) or i32
    // (0.17.0, `std.os.linux.waitpid`).
    const Status = if (builtin.link_libc) c_int else if (v17) i32 else u32;
    var status: Status = undefined;
    while (true) {
        const rc = system.waitpid(pid, &status, @intCast(flags));
        switch (posix.errno(rc)) {
            .SUCCESS => return .{ .pid = @intCast(rc), .status = @bitCast(status) },
            .INTR => continue,
            else => unreachable,
        }
    }
}

/// Monotonic clock in nanoseconds (the per-case deadline of common.zig's forkCall).
pub fn nowNs() u64 {
    var ts: posix.timespec = undefined;
    _ = system.clock_gettime(.MONOTONIC, &ts);
    return @as(u64, @intCast(ts.sec)) * 1_000_000_000 + @as(u64, @intCast(ts.nsec));
}

pub const PollResult = enum { readable, timeout, failed };

/// Waits up to `timeout_ms` for `fd` to be readable (data, EOF or hang-up).
pub fn pollReadable(fd: posix.fd_t, timeout_ms: i32) PollResult {
    var fds = [1]posix.pollfd{.{ .fd = fd, .events = posix.POLL.IN, .revents = 0 }};
    while (true) {
        const rc = system.poll(&fds, 1, timeout_ms);
        switch (posix.errno(rc)) {
            .SUCCESS => return if (rc == 0) .timeout else .readable,
            .INTR => continue,
            else => return .failed,
        }
    }
}

/// Containment for a forked tested call, best effort (a failed call leaves the child no worse
/// off than before): no core file (a crashing child must not feed `core_pattern` helpers such
/// as apport or systemd-coredump, a storm of thousands of crashes), a cap on the address space
/// (an undefined-behavior input must not take the host's memory; `mem_limit` bytes, 0 = none;
/// Linux only, macOS does not enforce RLIMIT_AS), and death with the parent (no orphan keeps
/// running, or holds the CI step's output pipe open, after the harness is killed).
pub fn containChild(mem_limit: u64) void {
    const no_core: posix.rlimit = .{ .cur = 0, .max = 0 };
    _ = system.setrlimit(.CORE, &no_core);
    if (is_linux) {
        _ = std.os.linux.prctl(@intFromEnum(std.os.linux.PR.SET_DUMPABLE), 0, 0, 0, 0);
        _ = std.os.linux.prctl(@intFromEnum(std.os.linux.PR.SET_PDEATHSIG), @intFromEnum(posix.SIG.KILL), 0, 0, 0);
        if (mem_limit != 0) {
            const cap: posix.rlimit = .{ .cur = mem_limit, .max = mem_limit };
            _ = system.setrlimit(.AS, &cap);
        }
    }
}

pub fn exit(status: u8) noreturn {
    if (!v16) posix.exit(status);
    if (is_linux) std.os.linux.exit_group(status);
    system.exit(status);
}

pub fn abort() noreturn {
    if (!v16) posix.abort();
    // No raw abort syscall; this path is a harness-bug branch only (a panic outside a forked
    // child), never exercised by a passing test run. 134 = 128 + SIGABRT, the shell convention.
    if (is_linux) std.os.linux.exit_group(134);
    system.abort();
}

/// Redirects fd 2 (stderr) to /dev/null, best-effort: a failure here is not fatal, it just lets
/// whatever noise the generic panic path writes through instead (common.zig's forkCall child).
pub fn silenceStderr() void {
    const devnull = if (v16)
        std.Io.Dir.openFileAbsolute(ioCtx(), "/dev/null", .{ .mode = .write_only })
    else
        std.fs.openFileAbsolute("/dev/null", .{ .mode = .write_only });
    if (devnull) |f| {
        dup2(f.handle, posix.STDERR_FILENO) catch {};
    } else |_| {}
}

// -- filesystem (tests/diff/common.zig's forEachLine, tests/diff/gen_inputs.zig) ------------

pub fn makePath(path: []const u8) !void {
    if (v16) return std.Io.Dir.cwd().createDirPath(ioCtx(), path);
    return std.fs.cwd().makePath(path);
}

pub fn readFileAlloc(gpa: std.mem.Allocator, path: []const u8, max: usize) ![]u8 {
    if (v16) return std.Io.Dir.cwd().readFileAlloc(ioCtx(), path, gpa, .limited(max));
    return std.fs.cwd().readFileAlloc(gpa, path, max);
}

const FileT = if (v16) std.Io.File else std.fs.File;

/// A created output file with its own small buffered writer. `open` only sets `file`, so it is
/// safe to return by value; `writer` then lazily buffers into `self`'s own `buf`, so `self` must
/// stay at a stable address (a `var` local) from that call onward — the returned pointer, and
/// the writer's internal buffer pointer, both point into it. `close` assumes `writer` was called
/// first (true at every call site today: each `OutFile` is opened and written to exactly once).
pub const OutFile = struct {
    file: FileT,
    buf: [4096]u8 = undefined,
    w: FileT.Writer = undefined,

    pub fn open(path: []const u8) !OutFile {
        if (v16) return .{ .file = try std.Io.Dir.cwd().createFile(ioCtx(), path, .{}) };
        return .{ .file = try std.fs.cwd().createFile(path, .{}) };
    }

    pub fn writer(self: *OutFile) *std.Io.Writer {
        self.w = if (v16) self.file.writer(ioCtx(), &self.buf) else self.file.writer(&self.buf);
        return &self.w.interface;
    }

    pub fn close(self: *OutFile) void {
        self.w.interface.flush() catch |err|
            std.debug.panic("compat.OutFile.close: flush failed: {}", .{err});
        if (v16) self.file.close(ioCtx()) else self.file.close();
    }
};

/// tests/floatprobe/probe.zig's stdout writer: same shape as `OutFile.writer`, but the caller
/// supplies its own buffer and does its own `.flush()`, so no lazy-init/self-reference concern.
pub const StdoutWriter = FileT.Writer;

pub fn stdoutWriter(buffer: []u8) StdoutWriter {
    if (v16) return std.Io.File.stdout().writer(ioCtx(), buffer);
    return std.fs.File.stdout().writer(buffer);
}

// -- types (0.17.0) -------------------------------------------------------------------------

/// True from 0.17.0 onward: `@typeInfo` struct info is struct-of-arrays (`field_names`,
/// `field_types`) instead of one `fields` array, and `std.meta.Int` is gone.
const v17 = builtin.zig_version.minor >= 17;

/// The unsigned integer type with `@bitSizeOf(T)` bits: `std.meta.Int(.unsigned, …)` before
/// 0.17.0, which removed it for `@Int` (a builtin that 0.15.2 does not parse).
pub fn Bits(comptime T: type) type {
    return std.math.IntFittingRange(0, (1 << @bitSizeOf(T)) - 1);
}

/// The number of fields of the struct (or tuple) `T`.
pub fn fieldCount(comptime T: type) usize {
    const s = @typeInfo(T).@"struct";
    return if (v17) s.field_names.len else s.fields.len;
}

/// The name of field `i` of the struct (or tuple) `T`.
pub fn fieldName(comptime T: type, comptime i: usize) [:0]const u8 {
    const s = @typeInfo(T).@"struct";
    return if (v17) s.field_names[i] else s.fields[i].name;
}

/// The type of field `i` of the struct (or tuple) `T`.
pub fn FieldType(comptime T: type, comptime i: usize) type {
    const s = @typeInfo(T).@"struct";
    return if (v17) s.field_types[i] else s.fields[i].type;
}
