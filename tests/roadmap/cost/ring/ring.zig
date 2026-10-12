//! P06 queue-operation bounds: a ring-buffer queue of `u32` with a fixed capacity.
//!
//! The queue is the buffer `buf`, the index `head` of the oldest item and the item count `len`.

const cap = 8;

/// Appends `x` unless the queue is full; returns whether it did.
export fn push(buf: *[cap]u32, head: *u32, len: *u32, x: u32) bool {
    if (len.* == cap) return false;
    buf[(head.* + len.*) % cap] = x;
    len.* += 1;
    return true;
}

/// Removes every item and returns their sum: one loop iteration per item.
export fn drain(buf: *[cap]u32, head: *u32, len: *u32) u64 {
    var sum: u64 = 0;
    while (len.* != 0) {
        sum += buf[head.*];
        head.* = (head.* + 1) % cap;
        len.* -= 1;
    }
    return sum;
}
