//! P04/P06: a fixed-capacity FIFO queue of `u32` items, a ring buffer over a caller's buffer.
//! `push`, `pop` and `count` are the queue's interface (the contract `Zig.Full.QueueImpl`,
//! ZigLean/Sep/Full/Queue.lean); `rotate` and `pushAll` are clients that use only that interface.
//! Every index and every add is checked (ReleaseSafe): the proofs show that no check fails.

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

comptime {
    _ = &Ring.init;
    _ = &Ring.count;
    _ = &Ring.push;
    _ = &Ring.pop;
    _ = &rotate;
    _ = &pushAll;
}
