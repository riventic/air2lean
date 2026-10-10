const std = @import("std");

var buffer: [4096]u8 = undefined;

pub export fn arena_sum(n: usize) u64 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return 0;
    @memset(s, 1);
    var sum: u64 = 0;
    for (s) |b| sum += b;
    a.free(s);
    return sum;
}

pub export fn arena_resize(n: usize, m: usize) bool {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return false;
    return a.resize(s, m);
}

pub export fn arena_reset(n: usize, retain: bool) usize {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    _ = a.alloc(u8, n) catch return 0;
    _ = a.alloc(u8, n) catch return 1;
    const ok = arena.reset(if (retain) .retain_capacity else .free_all);
    const t = a.alloc(u8, n) catch return 2;
    return @intFromBool(ok) + 2 * t.len + 4 * arena.queryCapacity();
}

/// Two live allocations must not overlap: 1 + 10 * 2 = 21 (`mutant.sh` breaks this).
pub export fn arena_two(n: usize) u64 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return 0;
    const t = a.alloc(u8, n) catch return 1;
    @memset(s, 1);
    @memset(t, 2);
    return @as(u64, s[0]) + 10 * @as(u64, t[0]);
}

pub export fn arena_page(n: usize) u64 {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const p = a.create(u64) catch return 0;
    p.* = n;
    const s = a.alloc(u8, n) catch return 1;
    @memset(s, 2);
    return p.* + s[0];
}

/// Frees a slice that the arena did not issue while the arena has no node: `free` unwraps the
/// empty `used_list` (`loadFirstNode().?`) and panics (obstruction O-A, `ArenaObstruction.lean`).
pub export fn arena_foreign_free() void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const foreign: []u8 = buffer[0..8];
    arena.allocator().free(foreign);
}

var node_buf: [8]u64 = undefined;

/// The state that a failed `alloc` leaves (obstruction O-E): the first node's `end_index` past
/// its buffer. Built by hand: the translated `alloc` is a `partial_fixpoint` group, which the
/// kernel does not evaluate. `free` then forms `buf_ptr + end_index` out of bounds
/// (`ArenaObstruction.lean`; natively undefined behaviour, `docs/upstream/arena-oob-gep.md`).
pub export fn arena_oob_free() void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const NodePtr = @typeInfo(@TypeOf(arena.state.used_list)).optional.child;
    const node: NodePtr = @ptrCast(&node_buf);
    node.* = .{ .size = @bitCast(@as(usize, @sizeOf(@TypeOf(node_buf)))), .end_index = 1000, .next = null };
    arena.state.used_list = node;
    const foreign: []u8 = buffer[0..8];
    arena.allocator().free(foreign);
}
