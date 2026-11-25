//! P04/P06: two fixed-capacity FIFO queues over a caller's buffer: `Ring`, a ring buffer of `u32`
//! items whose operations run no loop, and `Shift`, a linear array of `u16` items whose `pop`
//! moves the rest down, one loop-body run per item. `push`, `pop` and `count` are the queue's
//! interface (the contract `Zig.Full.QueueImpl`, ZigLean/Sep/Full/Queue.lean, with each
//! operation's declared step count); `rotate`, `pushAll` and `rotateShift` are clients that use
//! only that interface. Every index and every add is checked (ReleaseSafe): the proofs show that
//! no check fails.

pub const Ring = struct {
    /// The buffer; its length is the capacity.
    items: []u32,
    /// The index of the front item (below the capacity, or 0 for a capacity of 0).
    head: usize,
    /// The number of items.
    len: usize,

    /// An empty queue over `buf`.
    pub fn init(buf: []u32) Ring {
        return .{ .items = buf, .head = 0, .len = 0 };
    }

    /// The number of items.
    pub fn count(q: *const Ring) usize {
        return q.len;
    }

    /// Puts `v` at the back, or fails when the queue is full. The back is `len` places after
    /// `head`, around the end of the buffer.
    pub fn push(q: *Ring, v: u32) error{Full}!void {
        const cap = q.items.len;
        if (q.len == cap) return error.Full;
        const room = cap - q.head;
        const i = if (q.len < room) q.head + q.len else q.len - room;
        q.items[i] = v;
        q.len += 1;
    }

    /// Takes the front item, or null when the queue is empty.
    pub fn pop(q: *Ring) ?u32 {
        if (q.len == 0) return null;
        const v = q.items[q.head];
        const next = q.head + 1;
        q.head = if (next == q.items.len) 0 else next;
        q.len -= 1;
        return v;
    }
};

/// Client 1: moves the front item to the back (nothing for an empty queue). After the `pop`
/// there is room, so the `push` cannot fail.
pub fn rotate(q: *Ring) void {
    if (q.pop()) |v| q.push(v) catch unreachable;
}

/// Client 2: pushes the items of `vs` in order until the queue is full; the number pushed.
/// With room for all of them it runs its loop body `vs.len + 1` times.
pub fn pushAll(q: *Ring, vs: []const u32) usize {
    var n: usize = 0;
    while (n < vs.len) : (n += 1) q.push(vs[n]) catch break;
    return n;
}

/// The second implementation: the items are the first `len` cells, front first.
pub const Shift = struct {
    /// The buffer; its length is the capacity.
    items: []u16,
    /// The number of items.
    len: usize,

    /// An empty queue over `buf`.
    pub fn init(buf: []u16) Shift {
        return .{ .items = buf, .len = 0 };
    }

    /// The number of items.
    pub fn count(q: *const Shift) usize {
        return q.len;
    }

    /// Puts `v` at the back, or fails when the queue is full.
    pub fn push(q: *Shift, v: u16) error{Full}!void {
        if (q.len == q.items.len) return error.Full;
        q.items[q.len] = v;
        q.len += 1;
    }

    /// Takes the front item, or null when the queue is empty. Every other item moves one cell
    /// down: the loop body runs once per item (once per move and for the final test).
    pub fn pop(q: *Shift) ?u16 {
        if (q.len == 0) return null;
        const v = q.items[0];
        var i: usize = 1;
        while (i < q.len) : (i += 1) q.items[i - 1] = q.items[i];
        q.len -= 1;
        return v;
    }
};

/// Client 1 on the second implementation: the same program as `rotate`.
pub fn rotateShift(q: *Shift) void {
    if (q.pop()) |v| q.push(v) catch unreachable;
}

comptime {
    _ = &Shift.init;
    _ = &Shift.count;
    _ = &Shift.push;
    _ = &Shift.pop;
    _ = &rotateShift;
    _ = &Ring.init;
    _ = &Ring.count;
    _ = &Ring.push;
    _ = &Ring.pop;
    _ = &rotate;
    _ = &pushAll;
}
