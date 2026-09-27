//! M16a: single pointers `*T` and `?*T`, and locals whose address escapes.

pub const Job = struct {
    duration: u32,
    due: u32,
    weight: u8,
};

/// Swap two values. `swap(p, p)` leaves the value unchanged.
pub fn swap(a: *u32, b: *u32) void {
    const t = a.*;
    a.* = b.*;
    b.* = t;
}

/// Add `d` to the job's duration (overflow panics).
pub fn delay(j: *Job, d: u32) void {
    j.duration += d;
}

/// The pointer to the larger value, or the one that is not null.
pub fn maxPtr(a: ?*const u32, b: ?*const u32) ?*const u32 {
    const pa = a orelse return b;
    const pb = b orelse return a;
    return if (pa.* >= pb.*) pa else pb;
}

/// A pointer into the argument.
pub fn dueOf(j: *Job) *u32 {
    return &j.due;
}

fn addTo(acc: *u64, x: u32) void {
    acc.* += x;
}

/// A local whose address goes to `addTo`, in a loop.
pub fn sumTo(n: u32) u64 {
    var acc: u64 = 0;
    var i: u32 = 0;
    while (i < n) : (i += 1) addTo(&acc, i);
    return acc;
}

/// Copy a whole struct through pointers.
pub fn copyJob(dst: *Job, src: *const Job) void {
    dst.* = src.*;
}

/// Add 1 to the value behind `p`, if it is not null.
pub fn bumpOpt(p: *?u32) void {
    if (p.*) |*v| v.* += 1;
}

/// Set the optional behind `p` to `x`, or to null.
pub fn setOpt(p: *?u32, x: ?u32) void {
    p.* = x;
}

/// Pointer equality: the same block and offset.
pub fn same(a: *const u32, b: *const u32) bool {
    return a == b;
}

/// Build the job in place in the optional behind `p` (`optional_payload_ptr_set`).
pub fn setOptJob(p: *?Job, d: u32) void {
    p.* = .{ .duration = d, .due = 2, .weight = 3 };
}

/// Add n, n-1, …, 1 to the value behind `acc`, by recursion.
pub fn addDown(acc: *u64, n: u32) void {
    if (n == 0) return;
    acc.* += n;
    addDown(acc, n - 1);
}

comptime {
    _ = &setOptJob;
    _ = &addDown;
    _ = &bumpOpt;
    _ = &setOpt;
    _ = &same;
    _ = &swap;
    _ = &delay;
    _ = &maxPtr;
    _ = &dueOf;
    _ = &sumTo;
    _ = &copyJob;
}
