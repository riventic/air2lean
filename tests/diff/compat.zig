//! Version compat shim for Zig 0.15.2 vs 0.16.0 (0.14.1's writers, and 0.17.0's type reflection,
//! at the end) —
//! the only file in tests/diff/ and
//! tests/floatprobe/ with a Zig-version or OS switch; every other file there imports this and
//! stays version-agnostic. 0.16.0 removed std.posix's process layer (fork/pipe/write/waitpid/
//! dup2/exit/abort/close — `read` and `std.posix.{W,errno,system,fd_t,STDERR_FILENO}` are
//! unchanged and used directly by callers), replaced std.fs.{Dir,File,cwd()} with
//! std.Io.{Dir,File} plus an explicit `Io` execution context, and renamed
//! std.heap.GeneralPurposeAllocator to DebugAllocator (an unconditional rename, handled at each
//! call site instead of here).
//!
//! macOS and Linux, plus the Windows process layer of the harness (`win`, `WinChild`;
//! docs/windows-target.md): Windows has no fork, so common.zig runs the cases of one function in
//! a child process and restarts it after a case that ends it. No wasi paths.
//!
//! Imported directly (same directory) by common.zig and gen_inputs.zig; wired in as the
//! `compat` module for tests/floatprobe/probe.zig (scripts/floatprobe.sh), which lives
//! elsewhere.

const std = @import("std");
const builtin = @import("builtin");
const is_linux = builtin.os.tag == .linux;
pub const is_windows = builtin.os.tag == .windows;
const posix = std.posix;
const system = posix.system;

/// The descriptor of `write` and of the harness's result channel: a POSIX file descriptor, or a
/// Windows `HANDLE`.
pub const Fd = posix.fd_t;

/// True from 0.16.0 onward. Comptime-known, so `if (v16) ... else ...` below only ever
/// semantically analyzes the branch that applies to the Zig compiling this file.
const v16 = builtin.zig_version.minor >= 16;

/// True from 0.15.0 onward: `std.Io.Writer`, the buffered writer interface. Zig 0.14.1 has the
/// generic `std.io` writers instead; `Writer` and `Allocating` below give both the same shape.
const v15 = builtin.zig_version.minor >= 15;

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

pub fn write(fd: Fd, bytes: []const u8) !usize {
    if (is_windows) {
        var written: win.DWORD = 0;
        const n: win.DWORD = @intCast(@min(bytes.len, 1 << 30));
        if (win.WriteFile(fd, bytes.ptr, n, &written, null) == 0) return error.Unexpected;
        return written;
    }
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
    if (is_windows) return win.GetTickCount64() * std.time.ns_per_ms;
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

/// A signal's number: 0.15.2's `SIG` members are plain integers, 0.16.0's are enum values.
fn sigNumber(sig: anytype) usize {
    return if (@typeInfo(@TypeOf(sig)) == .@"enum") @intFromEnum(sig) else sig;
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
        _ = std.os.linux.prctl(@intFromEnum(std.os.linux.PR.SET_PDEATHSIG), sigNumber(posix.SIG.KILL), 0, 0, 0);
        if (mem_limit != 0) {
            const cap: posix.rlimit = .{ .cur = mem_limit, .max = mem_limit };
            _ = system.setrlimit(.AS, &cap);
        }
    }
}

pub fn exit(status: u8) noreturn {
    if (is_windows) win.ExitProcess(status);
    if (!v16) posix.exit(status);
    if (is_linux) std.os.linux.exit_group(status);
    system.exit(status);
}

pub fn abort() noreturn {
    if (is_windows) win.ExitProcess(134);
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

/// The empty signal mask (`std.posix.sigemptyset()`; 0.14.1: `std.posix.empty_sigset`).
pub fn emptySigset() posix.sigset_t {
    return if (v15) posix.sigemptyset() else posix.empty_sigset;
}

/// The alignment argument of `Allocator.alignedAlloc` for `bytes` (0.14.1: a `u29`).
pub fn alignment(comptime bytes: usize) if (v15) std.mem.Alignment else u29 {
    return if (v15) comptime .fromByteUnits(bytes) else bytes;
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

/// The writer that common.zig renders into: `std.Io.Writer`, or on 0.14.1 a type-erased
/// `std.io.AnyWriter` with the methods common.zig calls.
pub const Writer = if (v15) std.Io.Writer else struct {
    any: std.io.AnyWriter,

    pub fn print(self: *@This(), comptime format: []const u8, args: anytype) !void {
        try self.any.print(format, args);
    }
    pub fn writeAll(self: *@This(), bytes: []const u8) !void {
        try self.any.writeAll(bytes);
    }
    pub fn writeByte(self: *@This(), byte: u8) !void {
        try self.any.writeByte(byte);
    }
};

/// A `Writer` into memory (`std.Io.Writer.Allocating`); its writer is `allocatingWriter`.
pub const Allocating = if (v15) std.Io.Writer.Allocating else struct {
    list: std.ArrayList(u8),
    // `AnyWriter` points at its generic writer's context: both live here.
    gw: std.ArrayList(u8).Writer = undefined,
    w: Writer = undefined,

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{ .list = std.ArrayList(u8).init(allocator) };
    }
    pub fn deinit(self: *@This()) void {
        self.list.deinit();
    }
    pub fn written(self: *@This()) []u8 {
        return self.list.items;
    }
};

/// `aw`'s writer; `aw` must stay at a stable address (a `var` local) while it is used.
pub fn allocatingWriter(aw: *Allocating) *Writer {
    if (v15) return &aw.writer;
    aw.gw = aw.list.writer();
    aw.w = .{ .any = aw.gw.any() };
    return &aw.w;
}

const Buffered = if (v15) FileT.Writer else std.io.BufferedWriter(4096, std.fs.File.Writer);

/// A created output file with its own small buffered writer. `open` only sets `file`, so it is
/// safe to return by value; `writer` then lazily buffers into `self`'s own `buf`, so `self` must
/// stay at a stable address (a `var` local) from that call onward — the returned pointer, and
/// the writer's internal buffer pointer, both point into it. `close` assumes `writer` was called
/// first (true at every call site today: each `OutFile` is opened and written to exactly once).
pub const OutFile = struct {
    file: FileT,
    buf: [4096]u8 = undefined,
    w: Buffered = undefined,
    // 0.14.1: the generic writer whose context `any` points at.
    gw: if (v15) void else Buffered.Writer = undefined,
    any: Writer = undefined,

    pub fn open(path: []const u8) !OutFile {
        if (v16) return .{ .file = try std.Io.Dir.cwd().createFile(ioCtx(), path, .{}) };
        return .{ .file = try std.fs.cwd().createFile(path, .{}) };
    }

    pub fn writer(self: *OutFile) *Writer {
        if (!v15) {
            self.w = .{ .unbuffered_writer = self.file.writer() };
            self.gw = self.w.writer();
            self.any = .{ .any = self.gw.any() };
            return &self.any;
        }
        self.w = if (v16) self.file.writer(ioCtx(), &self.buf) else self.file.writer(&self.buf);
        return &self.w.interface;
    }

    pub fn close(self: *OutFile) void {
        (if (v15) self.w.interface.flush() else self.w.flush()) catch |err|
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

/// The process's standard output (`write`'s descriptor).
pub fn stdoutFd() Fd {
    if (is_windows) return win.GetStdHandle(win.STD_OUTPUT_HANDLE).?;
    return 1;
}

/// A `Writer` that drops what it is given: the output of a Windows case child, which reports its
/// results through its own channel (common.zig).
pub const Discard = struct {
    buf: [64]u8 = undefined,
    impl: if (v15) std.Io.Writer.Discarding else void = undefined,
    w: if (v15) void else Writer = undefined,

    pub fn writer(self: *Discard) *Writer {
        if (!v15) {
            self.w = .{ .any = std.io.null_writer.any() };
            return &self.w;
        }
        self.impl = std.Io.Writer.Discarding.init(&self.buf);
        return &self.impl.writer;
    }
};

// -- Windows process layer (docs/windows-target.md) -------------------------------------------

/// kernel32, declared here with the same types on every Zig version (std's Windows bindings
/// move between versions). Only referenced when the target is Windows.
pub const win = struct {
    pub const HANDLE = *anyopaque;
    pub const BOOL = i32;
    pub const DWORD = u32;
    pub const STD_INPUT_HANDLE: DWORD = @bitCast(@as(i32, -10));
    pub const STD_OUTPUT_HANDLE: DWORD = @bitCast(@as(i32, -11));
    pub const STD_ERROR_HANDLE: DWORD = @bitCast(@as(i32, -12));
    pub const STARTF_USESTDHANDLES: DWORD = 0x100;
    pub const HANDLE_FLAG_INHERIT: DWORD = 1;
    pub const WAIT_OBJECT_0: DWORD = 0;
    pub const SECURITY_ATTRIBUTES = extern struct {
        nLength: DWORD,
        lpSecurityDescriptor: ?*anyopaque,
        bInheritHandle: BOOL,
    };
    pub const STARTUPINFOW = extern struct {
        cb: DWORD,
        lpReserved: ?[*:0]u16 = null,
        lpDesktop: ?[*:0]u16 = null,
        lpTitle: ?[*:0]u16 = null,
        dwX: DWORD = 0,
        dwY: DWORD = 0,
        dwXSize: DWORD = 0,
        dwYSize: DWORD = 0,
        dwXCountChars: DWORD = 0,
        dwYCountChars: DWORD = 0,
        dwFillAttribute: DWORD = 0,
        dwFlags: DWORD = 0,
        wShowWindow: u16 = 0,
        cbReserved2: u16 = 0,
        lpReserved2: ?*u8 = null,
        hStdInput: ?HANDLE = null,
        hStdOutput: ?HANDLE = null,
        hStdError: ?HANDLE = null,
    };
    pub const PROCESS_INFORMATION = extern struct {
        hProcess: HANDLE,
        hThread: HANDLE,
        dwProcessId: DWORD,
        dwThreadId: DWORD,
    };
    pub extern "kernel32" fn GetStdHandle(n: DWORD) callconv(.winapi) ?HANDLE;
    pub extern "kernel32" fn WriteFile(h: HANDLE, buf: [*]const u8, n: DWORD, written: ?*DWORD, ov: ?*anyopaque) callconv(.winapi) BOOL;
    pub extern "kernel32" fn ReadFile(h: HANDLE, buf: [*]u8, n: DWORD, read: ?*DWORD, ov: ?*anyopaque) callconv(.winapi) BOOL;
    pub extern "kernel32" fn PeekNamedPipe(h: HANDLE, buf: ?*anyopaque, n: DWORD, read: ?*DWORD, avail: ?*DWORD, left: ?*DWORD) callconv(.winapi) BOOL;
    pub extern "kernel32" fn CreatePipe(r: *HANDLE, w: *HANDLE, sa: ?*const SECURITY_ATTRIBUTES, size: DWORD) callconv(.winapi) BOOL;
    pub extern "kernel32" fn SetHandleInformation(h: HANDLE, mask: DWORD, flags: DWORD) callconv(.winapi) BOOL;
    pub extern "kernel32" fn CreateProcessW(app: ?[*:0]const u16, cmd: [*:0]u16, pa: ?*anyopaque, ta: ?*anyopaque, inherit: BOOL, flags: DWORD, env: ?*anyopaque, cwd: ?[*:0]const u16, si: *STARTUPINFOW, pi: *PROCESS_INFORMATION) callconv(.winapi) BOOL;
    pub extern "kernel32" fn WaitForSingleObject(h: HANDLE, ms: DWORD) callconv(.winapi) DWORD;
    pub extern "kernel32" fn GetExitCodeProcess(h: HANDLE, code: *DWORD) callconv(.winapi) BOOL;
    pub extern "kernel32" fn TerminateProcess(h: HANDLE, code: u32) callconv(.winapi) BOOL;
    pub extern "kernel32" fn CloseHandle(h: HANDLE) callconv(.winapi) BOOL;
    pub extern "kernel32" fn GetModuleFileNameW(m: ?HANDLE, buf: [*]u16, n: DWORD) callconv(.winapi) DWORD;
    pub extern "kernel32" fn GetCommandLineW() callconv(.winapi) [*:0]const u16;
    pub extern "kernel32" fn Sleep(ms: DWORD) callconv(.winapi) void;
    pub extern "kernel32" fn GetTickCount64() callconv(.winapi) u64;
    pub extern "kernel32" fn ExitProcess(code: u32) callconv(.winapi) noreturn;
};

/// The command-line flag that makes a harness a case child: `--air2lean-child <case> <line>`.
const child_flag = "--air2lean-child";

/// The case child's assignment: run the inputs of `name` (`<ex>/<fn>`) from input line `start`
/// (1-based) on. `null` in the supervising process and on every other OS.
pub const ChildCase = struct { name: []const u8, start: usize };

var child_case_buf: [256]u8 = undefined;

pub fn childCase() ?ChildCase {
    if (!is_windows) return null;
    const line = std.mem.span(win.GetCommandLineW());
    // The command line is ASCII from `WinChild.spawn`; anything else is not a child's.
    var ascii: [512]u8 = undefined;
    if (line.len > ascii.len) return null;
    for (line, 0..) |c, i| ascii[i] = if (c < 0x80) @intCast(c) else '?';
    const text = ascii[0..line.len];
    const at = std.mem.indexOf(u8, text, " " ++ child_flag ++ " ") orelse return null;
    var it = std.mem.tokenizeScalar(u8, text[at + child_flag.len + 2 ..], ' ');
    const name = it.next() orelse return null;
    const start = std.fmt.parseInt(usize, it.next() orelse return null, 10) catch return null;
    if (name.len > child_case_buf.len) return null;
    @memcpy(child_case_buf[0..name.len], name);
    return .{ .name = child_case_buf[0..name.len], .start = start };
}

/// A case child of this harness: the same executable with `--air2lean-child <case> <line>`, its
/// standard output a pipe that the supervisor reads (common.zig's `superviseCases`).
pub const WinChild = struct {
    process: win.HANDLE,
    out: win.HANDLE,

    pub fn spawn(case: []const u8, start: usize) !WinChild {
        var exe: [1024]u16 = undefined;
        const exe_len = win.GetModuleFileNameW(null, &exe, exe.len);
        if (exe_len == 0 or exe_len >= exe.len) return error.SpawnFailed;
        var args_buf: [320]u8 = undefined;
        const args = try std.fmt.bufPrint(&args_buf, " " ++ child_flag ++ " {s} {d}", .{ case, start });
        var cmd: [1024 + 2 + 320 + 1:0]u16 = undefined;
        var n: usize = 0;
        cmd[n] = '"';
        n += 1;
        for (exe[0..exe_len]) |c| {
            cmd[n] = c;
            n += 1;
        }
        cmd[n] = '"';
        n += 1;
        for (args) |c| {
            cmd[n] = c;
            n += 1;
        }
        cmd[n] = 0;
        const sa: win.SECURITY_ATTRIBUTES = .{ .nLength = @sizeOf(win.SECURITY_ATTRIBUTES), .lpSecurityDescriptor = null, .bInheritHandle = 1 };
        var read_end: win.HANDLE = undefined;
        var write_end: win.HANDLE = undefined;
        if (win.CreatePipe(&read_end, &write_end, &sa, 1 << 16) == 0) return error.SpawnFailed;
        defer _ = win.CloseHandle(write_end);
        errdefer _ = win.CloseHandle(read_end);
        if (win.SetHandleInformation(read_end, win.HANDLE_FLAG_INHERIT, 0) == 0) return error.SpawnFailed;
        var si: win.STARTUPINFOW = .{ .cb = @sizeOf(win.STARTUPINFOW), .dwFlags = win.STARTF_USESTDHANDLES,
            .hStdInput = win.GetStdHandle(win.STD_INPUT_HANDLE), .hStdOutput = write_end,
            .hStdError = win.GetStdHandle(win.STD_ERROR_HANDLE) };
        var pi: win.PROCESS_INFORMATION = undefined;
        if (win.CreateProcessW(null, cmd[0..n :0], null, null, 1, 0, null, null, &si, &pi) == 0)
            return error.SpawnFailed;
        _ = win.CloseHandle(pi.hThread);
        return .{ .process = pi.hProcess, .out = read_end };
    }

    /// Appends the bytes the child has written so far; `false` when there were none.
    pub fn readAvailable(self: WinChild, gpa: std.mem.Allocator, into: *std.ArrayListUnmanaged(u8)) !bool {
        var avail: win.DWORD = 0;
        if (win.PeekNamedPipe(self.out, null, 0, null, &avail, null) == 0 or avail == 0) return false;
        var chunk: [4096]u8 = undefined;
        var got: win.DWORD = 0;
        if (win.ReadFile(self.out, &chunk, @min(avail, chunk.len), &got, null) == 0) return false;
        try into.appendSlice(gpa, chunk[0..got]);
        return got != 0;
    }

    /// The exit code once the child has ended; `null` while it runs.
    pub fn exitCode(self: WinChild) ?u32 {
        if (win.WaitForSingleObject(self.process, 0) != win.WAIT_OBJECT_0) return null;
        var code: win.DWORD = 0;
        if (win.GetExitCodeProcess(self.process, &code) == 0) return 0xffff_ffff;
        return code;
    }

    pub fn kill(self: WinChild) void {
        _ = win.TerminateProcess(self.process, 1);
        _ = win.WaitForSingleObject(self.process, 0xffff_ffff);
    }

    pub fn close(self: WinChild) void {
        _ = win.CloseHandle(self.out);
        _ = win.CloseHandle(self.process);
    }
};

/// The legacy fault name of a Windows exception exit code (the POSIX signal of the same fault),
/// so the native outcome is the one `scripts/panic-policy.tsv` maps on every OS; `null` for
/// another code.
pub fn windowsFault(code: u32) ?[]const u8 {
    return switch (code) {
        0xC0000094, 0xC0000095 => "SIGFPE", // integer divide by zero, integer overflow (`div`)
        0xC000001D => "SIGILL", // illegal instruction (`ud2`)
        0xC0000005 => "SIGSEGV", // access violation
        0x80000002 => "SIGBUS", // datatype misalignment
        else => null,
    };
}

pub fn sleepMs(ms: u32) void {
    if (is_windows) win.Sleep(ms);
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
