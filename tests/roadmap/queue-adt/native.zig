//! The native run of queue.zig that check.sh compares with expected.txt: the ring's operations
//! on a buffer of four cells, across the end of the buffer (wrap-around), when full and when
//! empty, and the two clients.
const std = @import("std");
const queue = @import("queue.zig");

fn show(tag: []const u8, q: *queue.Ring) void {
    std.debug.print("{s}: head {d} len {d} cells", .{ tag, q.head, q.len });
    for (q.items) |c| std.debug.print(" {d}", .{c});
    std.debug.print("\n", .{});
}

fn ok(r: error{Full}!void) u8 {
    r catch return 0;
    return 1;
}

pub fn main() void {
    var buf = [_]u32{ 0, 0, 0, 0 };
    var q = queue.Ring.init(&buf);
    std.debug.print("empty: count {d} pop {?d}\n", .{ q.count(), q.pop() });

    // fill, then one more
    std.debug.print("push {d} {d} {d} {d} full {d}\n", .{ ok(q.push(1)), ok(q.push(2)), ok(q.push(3)), ok(q.push(4)), ok(q.push(5)) });
    show("full", &q);

    // around the end: two out, two in
    std.debug.print("pop {?d} {?d}\n", .{ q.pop(), q.pop() });
    std.debug.print("push {d} {d} count {d}\n", .{ ok(q.push(6)), ok(q.push(7)), q.count() });
    show("wrapped", &q);

    // client 1
    queue.rotate(&q);
    show("rotated", &q);

    // drain in order
    std.debug.print("pop {?d} {?d} {?d} {?d} {?d}\n", .{ q.pop(), q.pop(), q.pop(), q.pop(), q.pop() });
    show("drained", &q);
    queue.rotate(&q);
    show("rotated empty", &q);

    // client 2: with room for every item, then without
    const three = [_]u32{ 10, 11, 12 };
    std.debug.print("pushAll {d}\n", .{queue.pushAll(&q, &three)});
    show("three", &q);
    std.debug.print("pushAll {d}\n", .{queue.pushAll(&q, &three)});
    show("four", &q);
    std.debug.print("pop {?d} {?d} {?d} {?d} {?d}\n", .{ q.pop(), q.pop(), q.pop(), q.pop(), q.pop() });

    // a ring without cells is full and empty
    var none = queue.Ring.init(buf[0..0]);
    std.debug.print("no cells: push {d} pop {?d} count {d}\n", .{ ok(none.push(1)), none.pop(), none.count() });
}
