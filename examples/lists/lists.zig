//! M18: allocators, heap memory, `std.ArrayListUnmanaged` and a linked list.

const std = @import("std");
const Allocator = std.mem.Allocator;
/// Zig 0.17.0 removed `Allocator.dupeZ` (it called `dupeSentinel(T, m, 0)`); 0.15.2 has no
/// `dupeSentinel`.
const has_dupe_z = @hasDecl(Allocator, "dupeZ");

pub const Node = struct {
    val: u32,
    next: ?*Node,
};

/// A new node on the heap, in front of `next`.
pub fn push(a: Allocator, next: ?*Node, val: u32) !*Node {
    const n = try a.create(Node);
    n.* = .{ .val = val, .next = next };
    return n;
}

/// Reverse a list in place.
pub fn reverse(head: ?*Node) ?*Node {
    var prev: ?*Node = null;
    var cur = head;
    while (cur) |n| {
        cur = n.next;
        n.next = prev;
        prev = n;
    }
    return prev;
}

/// Free every node of a list.
pub fn freeAll(a: Allocator, head: ?*Node) void {
    var p = head;
    while (p) |n| {
        p = n.next;
        a.destroy(n);
    }
}

/// The sum of a list.
pub fn sum(head: ?*const Node) u64 {
    var s: u64 = 0;
    var p = head;
    while (p) |n| : (p = n.next) s += n.val;
    return s;
}

/// Push the items of `xs` on a list, reverse it, and return the first item times 2^32 plus the
/// sum. Frees the list, also when an allocation fails.
pub fn listSum(a: Allocator, xs: []const u32) !u64 {
    var head: ?*Node = null;
    defer freeAll(a, head);
    for (xs) |x| head = try push(a, head, x);
    head = reverse(head);
    const first: u64 = if (head) |n| n.val else 0;
    return (first << 32) + sum(head);
}

/// The sum of `0, 1, …, n - 1`, from items in a heap buffer.
pub fn sumRange(a: Allocator, n: usize) !u64 {
    const xs = try a.alloc(u32, n);
    defer a.free(xs);
    for (xs, 0..) |*x, i| x.* = @truncate(i);
    var s: u64 = 0;
    for (xs) |x| s += x;
    return s;
}

/// A copy of `xs` on the heap.
pub fn dupe(a: Allocator, xs: []const u8) ![]u8 {
    return a.dupe(u8, xs);
}

/// The length of a `dupeZ` copy of `xs` up to its first 0 (the sentinel, if `xs` has no 0).
/// `free` of the `[:0]u8` frees `len + 1` bytes.
pub fn dupeZLen(a: Allocator, xs: []const u8) !usize {
    const z = try if (has_dupe_z) a.dupeZ(u8, xs) else a.dupeSentinel(u8, xs, 0);
    defer a.free(z);
    var n: usize = 0;
    while (z[n] != 0) n += 1;
    return n;
}

/// The even items of `xs`, in a new slice (`std.ArrayListUnmanaged`).
pub fn evens(a: Allocator, xs: []const u32) ![]u32 {
    var list: std.ArrayListUnmanaged(u32) = .empty;
    errdefer list.deinit(a);
    for (xs) |x| {
        if (x % 2 == 0) try list.append(a, x);
    }
    return list.toOwnedSlice(a);
}

comptime {
    _ = &push;
    _ = &reverse;
    _ = &freeAll;
    _ = &sum;
    _ = &listSum;
    _ = &sumRange;
    _ = &dupe;
    _ = &dupeZLen;
    _ = &evens;
}
