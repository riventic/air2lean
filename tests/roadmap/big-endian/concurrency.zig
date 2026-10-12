//! T03: atomics, futexes, threads and the allocator model on a big-endian target. Every function
//! observes byte order: atomic values are read back through their bytes, and bytes written
//! plainly are read atomically. `concurrency_native.zig` prints each case; `ConcDiff.lean` prints
//! the model's lines.
const std = @import("std");

// The single-threaded cases work on globals: an atomic op on a local that does not escape is
// outside the translator's subset (the local is a Lean value).
var w32: u32 = 0;
var w16: u16 = 0;
var w64: u64 = 0;
var wi: i32 = 0;

/// An atomic store, then the bytes of the word.
pub fn storeThenBytes(x: u32) u32 {
    @atomicStore(u32, &w32, x, .seq_cst);
    const b: *const [4]u8 = @ptrCast(&w32);
    return @as(u32, b[0]) << 24 | @as(u32, b[1]) << 16 | @as(u32, b[2]) << 8 | b[3];
}

/// Bytes written plainly, then an atomic load of the word.
pub fn bytesThenLoad(b0: u8, b1: u8, b2: u8, b3: u8) u32 {
    const b: *[4]u8 = @ptrCast(&w32);
    b.* = .{ b0, b1, b2, b3 };
    return @atomicLoad(u32, &w32, .seq_cst);
}

/// An RMW add whose carry crosses a byte, then byte 0 of the word.
pub fn rmwCarryByte0(x: u16, y: u16) u8 {
    w16 = x;
    _ = @atomicRmw(u16, &w16, .Add, y, .seq_cst);
    const b: *const [2]u8 = @ptrCast(&w16);
    return b[0];
}

/// A `cmpxchg` on a 64-bit word: the expected value compares by value, not by bytes.
pub fn casSwap(x: u64, y: u64) u64 {
    w64 = x;
    const failed = @cmpxchgStrong(u64, &w64, x, y, .seq_cst, .seq_cst);
    return if (failed == null) w64 else 0;
}

/// A signed `Max` RMW on a 32-bit word.
pub fn rmwMax(x: i32, y: i32) i32 {
    wi = x;
    _ = @atomicRmw(i32, &wi, .Max, y, .seq_cst);
    return wi;
}

fn adder(c: *u32, n: u32) void {
    var i: u32 = 0;
    while (i < n) : (i += 1) _ = @atomicRmw(u32, c, .Add, 0x0101, .seq_cst);
}

/// Two threads add to one counter; the result's high byte is read through the bytes.
pub fn threadsAdd(n: u32) !u32 {
    var c: u32 = 0x00FF_0000;
    const t1 = try std.Thread.spawn(.{}, adder, .{ &c, n });
    const t2 = try std.Thread.spawn(.{}, adder, .{ &c, n });
    t1.join();
    t2.join();
    const b: *const [4]u8 = @ptrCast(&c);
    return @as(u32, b[0]) << 24 | (@atomicLoad(u32, &c, .seq_cst) & 0x00FF_FFFF);
}

/// `std.Thread.Futex` (Zig 0.14.1, 0.15.2; 0.16.0 moved futexes to `std.Io`).
pub const has_futex = @hasDecl(std.Thread, "Futex");
const Futex = if (has_futex) std.Thread.Futex else void;

/// A futex wait whose expected value is the word's bytes in the other order: the kernel
/// compares values, so the wait returns at once (a byte-order mistake would sleep forever).
pub fn futexNoSleep() u32 {
    var word = std.atomic.Value(u32).init(0x0102_0304);
    Futex.wait(&word, 0x0403_0201);
    return word.load(.monotonic);
}

/// The allocator model: a heap word, written atomically, read through its bytes.
pub fn heapWord(a: std.mem.Allocator, x: u32) !u32 {
    const p = try a.create(u32);
    defer a.destroy(p);
    @atomicStore(u32, p, x, .seq_cst);
    const b: *const [4]u8 = @ptrCast(p);
    return @as(u32, b[0]) << 24 | @as(u32, b[3]);
}

comptime {
    _ = &storeThenBytes;
    _ = &bytesThenLoad;
    _ = &rmwCarryByte0;
    _ = &casSwap;
    _ = &rmwMax;
    _ = &threadsAdd;
    if (has_futex) _ = &futexNoSleep;
    _ = &heapWord;
}
