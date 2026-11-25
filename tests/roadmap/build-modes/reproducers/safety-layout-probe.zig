//! Probe: which type layouts depend on the build mode (runtime safety)?
//! (docs/architecture-audit/2026-11-25-build-modes-0171.md, BM-1 classification.)
//!
//! Prints `@sizeOf`/`@alignOf` (and an `@offsetOf` where a field follows the construct) of every
//! candidate construct. Run it in the four modes with each supported stock Zig and compare:
//!   for m in Debug ReleaseSafe ReleaseFast ReleaseSmall; do
//!     zig run -O$m tests/roadmap/build-modes/reproducers/safety-layout-probe.zig; done
//! (0.14.1 and 0.15.2 cannot link on current macOS: build with `-target aarch64-linux-musl` and
//! run the static binary in a `linux/arm64` container.)
//! A line that differs between ReleaseSafe and ReleaseFast/ReleaseSmall is a layout that the
//! ReleaseSafe model has and an unchecked build does not. The measured table is in the audit report.
//! Constructs absent from a version print nothing (`@hasDecl` guards), so one file serves
//! 0.14.1–0.17.1. The reified-union case is in `safety-layout-reify-*.zig` (its builtin differs).
const std = @import("std");
const builtin = @import("builtin");

fn row(comptime name: []const u8, comptime T: type) void {
    std.debug.print("{s:<44} size {d:>5} align {d:>3}\n", .{ name, @sizeOf(T), @alignOf(T) });
}

fn after(comptime name: []const u8, comptime T: type) void {
    // A field that follows the construct: its offset moves with the construct's size.
    const S = struct { x: T, tail: u8 };
    std.debug.print("{s:<44} @offsetOf(tail) {d:>5}\n", .{ name, @offsetOf(S, "tail") });
}

const Bare = union { int: u32, small: u8 };
const Tagged = union(enum) { int: u32, small: u8 };
const Ext = extern union { int: u32, small: u8 };
const Pck = packed union { int: u32, small: u32 };
const InBare = struct { n: Bare, tail: u8 };
// A user type selected by a comptime branch on the mode: invisible in the safe AIR.
const ModeInt = if (std.debug.runtime_safety) u64 else u32;

fn unsafeScopeUnion() type {
    @setRuntimeSafety(false);
    return union { int: u32, small: u8 };
}

fn safeScopeUnion() type {
    @setRuntimeSafety(true);
    return union { int: u32, small: u8 };
}

pub fn main() void {
    std.debug.print("mode {s}\n", .{@tagName(builtin.mode)});
    // Language constructs.
    row("bare union", Bare);
    row("struct containing a bare union", InBare);
    std.debug.print("{s:<44} @offsetOf(tail) {d:>5}\n", .{ "struct containing a bare union", @offsetOf(InBare, "tail") });
    row("bare union, @setRuntimeSafety(false) scope", unsafeScopeUnion());
    row("bare union, @setRuntimeSafety(true) scope", safeScopeUnion());
    row("tagged union", Tagged);
    row("extern union", Ext);
    row("packed union", Pck);
    row("?u32", ?u32);
    row("?*u32", ?*u32);
    row("[]u8", []u8);
    row("anyerror", anyerror);
    row("anyerror!u32", anyerror!u32);
    row("error{A}!u64", error{A}!u64);
    row("comptime branch on runtime_safety", ModeInt);
    // std.debug.
    if (@hasDecl(std.debug, "SafetyLock")) row("std.debug.SafetyLock", std.debug.SafetyLock);
    if (@hasDecl(std.debug, "Trace")) row("std.debug.Trace", std.debug.Trace);
    // Containers.
    row("std.ArrayList(u32)", std.ArrayList(u32));
    after("std.ArrayList(u32)", std.ArrayList(u32));
    if (@hasDecl(std, "ArrayListUnmanaged")) row("std.ArrayListUnmanaged(u32)", std.ArrayListUnmanaged(u32));
    row("std.AutoHashMapUnmanaged(u32,u32)", std.AutoHashMapUnmanaged(u32, u32));
    if (@hasDecl(std, "AutoHashMap")) row("std.AutoHashMap(u32,u32)", std.AutoHashMap(u32, u32));
    if (@hasDecl(std, "AutoArrayHashMapUnmanaged")) row("std.AutoArrayHashMapUnmanaged(u32,u32)", std.AutoArrayHashMapUnmanaged(u32, u32));
    if (@hasDecl(std, "array_hash_map") and @hasDecl(std.array_hash_map, "Auto")) row("std.array_hash_map.Auto(u32,u32)", std.array_hash_map.Auto(u32, u32));
    row("std.MultiArrayList(struct{a:u32})", std.MultiArrayList(struct { a: u32 }));
    // Synchronisation.
    if (@hasDecl(std.Thread, "Mutex")) row("std.Thread.Mutex", std.Thread.Mutex);
    if (@hasDecl(std.Thread, "Condition")) row("std.Thread.Condition", std.Thread.Condition);
    if (@hasDecl(std.Thread, "RwLock")) row("std.Thread.RwLock", std.Thread.RwLock);
    if (@hasDecl(std.Thread, "WaitGroup")) row("std.Thread.WaitGroup", std.Thread.WaitGroup);
    if (@hasDecl(std.Thread, "ResetEvent")) row("std.Thread.ResetEvent", std.Thread.ResetEvent);
    if (@hasDecl(std.Thread, "Semaphore")) row("std.Thread.Semaphore", std.Thread.Semaphore);
    if (@hasDecl(std, "Io")) {
        if (@hasDecl(std.Io, "Mutex")) row("std.Io.Mutex", std.Io.Mutex);
        if (@hasDecl(std.Io, "Condition")) row("std.Io.Condition", std.Io.Condition);
        if (@hasDecl(std.Io, "RwLock")) row("std.Io.RwLock", std.Io.RwLock);
        if (@hasDecl(std.Io, "Semaphore")) row("std.Io.Semaphore", std.Io.Semaphore);
        if (@hasDecl(std.Io, "Group")) row("std.Io.Group", std.Io.Group);
        if (@hasDecl(std.Io, "Threaded")) row("std.Io.Threaded", std.Io.Threaded);
    }
    // Allocators.
    if (@hasDecl(std.heap, "DebugAllocator")) row("std.heap.DebugAllocator(.{})", std.heap.DebugAllocator(.{}));
    if (@hasDecl(std.heap, "ArenaAllocator")) row("std.heap.ArenaAllocator", std.heap.ArenaAllocator);
    if (@hasDecl(std.heap, "FixedBufferAllocator")) row("std.heap.FixedBufferAllocator", std.heap.FixedBufferAllocator);
    if (@hasDecl(std.heap, "MemoryPool")) row("std.heap.MemoryPool(u64)", std.heap.MemoryPool(u64));
    if (@hasDecl(std.heap, "StackFallbackAllocator")) row("std.heap.StackFallbackAllocator(16)", std.heap.StackFallbackAllocator(16));
    // Other std state types with mode branches in their declaration.
    row("std.crypto.onetimeauth.Ghash", std.crypto.onetimeauth.Ghash);
    row("std.Random.DefaultPrng", std.Random.DefaultPrng);
}
