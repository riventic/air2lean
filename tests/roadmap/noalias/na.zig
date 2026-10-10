//! `noalias` parameters (docs/illegal-behavior.md, "noalias"). Zig lowers `noalias` to LLVM's
//! `noalias` argument attribute: during the call, memory accessed through a pointer based on the
//! parameter must not also be accessed through another pointer if either access writes. The
//! model gives `.illegal` for such a call (`Cases.lean`); `check.sh` exports the analyzed AIR
//! (ReleaseSafe), translates it and evaluates the generated Lean.

/// A `memcpy`-like copy, as compiler_rt's `memcpySmall`.
fn copy(noalias dest: [*]u8, noalias src: [*]const u8, len: usize) void {
    for (0..len) |i| dest[i] = src[i];
}

/// `copy` within one buffer: `dest` starts `shift` bytes after `src`. Overlapping (illegal) when
/// `shift < n`, disjoint when `shift >= n`.
pub fn shiftCopy(shift: usize, n: usize) u8 {
    var buf = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 };
    copy(buf[shift..].ptr, &buf, n);
    return buf[15];
}

/// `copy` between two buffers: never overlapping.
pub fn twoBuffers(n: usize) u8 {
    var a = [_]u8{ 1, 2, 3, 4 };
    var b = [_]u8{ 0, 0, 0, 0 };
    copy(&b, &a, n);
    return b[3];
}

/// `std.mem.swap`: both parameters `noalias`. Illegal for one pointer twice.
fn swap(noalias a: *u32, noalias b: *u32) void {
    const t = a.*;
    a.* = b.*;
    b.* = t;
}

pub fn swapSelf(same: bool) u32 {
    var x: u32 = 1;
    var y: u32 = 2;
    swap(&x, if (same) &x else &y);
    return x * 10 + y;
}

/// Two `noalias` parameters that only read: the same pointer twice is legal (no write).
fn sum(noalias a: *const u32, noalias b: *const u32) u32 {
    return a.* + b.*;
}

pub fn sumSelf() u32 {
    var x: u32 = 21;
    return sum(&x, &x);
}

/// A write through a `noalias` parameter and a read through a parameter without it: illegal
/// when both point to the same `u32`.
fn bumpThenRead(noalias p: *u32, q: *const u32) u32 {
    p.* += 1;
    return q.*;
}

pub fn bumpOther(same: bool) u32 {
    var x: u32 = 5;
    var y: u32 = 7;
    return bumpThenRead(&x, if (same) &x else &y);
}

fn sink(p: *u32) void {
    p.* = 0;
}

/// A `noalias` pointer passed on: the callee's accesses would not be checked against it, so
/// the translator rejects the function (`probe-air`, `expected.json`).
pub fn escape(noalias p: *u32) void {
    sink(p);
}

comptime {
    _ = &shiftCopy;
    _ = &twoBuffers;
    _ = &swapSelf;
    _ = &sumSelf;
    _ = &bumpOther;
    _ = &escape;
}
