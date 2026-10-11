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

/// Three live allocations must not overlap: 1 + 10 * 2 + 100 * 3 = 321. The first comes from a
/// new node, the others from its fast path, which reserves by bumping `end_index` (`mutant.sh`
/// removes the bump: the third allocation gets the second's bytes, 331).
pub export fn arena_three(n: usize) u64 {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    defer arena.deinit();
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return 0;
    const t = a.alloc(u8, n) catch return 1;
    const u = a.alloc(u8, n) catch return 2;
    @memset(s, 1);
    @memset(t, 2);
    @memset(u, 3);
    return @as(u64, s[0]) + 10 * @as(u64, t[0]) + 100 * @as(u64, u[0]);
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

var small: [256]u8 = undefined;

/// An allocation that the child cannot serve after one that it could, then the `free` of the
/// first slice (obstruction O-E from real runs, as `upstream/oob_gep.zig`). The stock arena keeps
/// the first node's `end_index` past its buffer and the translated `free` is illegal
/// (natively: undefined behaviour without a visible effect, so `true`); the patched arena
/// (`docs/upstream/arena-oob-gep.md`) gives the reservation back and frees the slice.
pub export fn arena_oom_free(n: usize) bool {
    var fba = std.heap.FixedBufferAllocator.init(&small);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return false;
    _ = a.alloc(u8, 4096) catch {};
    a.free(s);
    return true;
}

/// A request whose reservation `n + alignment - 1` exceeds the first node's buffer although the
/// aligned request fits it (the node is empty again: its only allocation was freed). The stock
/// arena reserves past the buffer and serves the request from the node; the patched arena does
/// not reserve and takes the place in its resize path (a retry there would never end). The node
/// is not grown: its capacity stays 60.
pub export fn arena_fit(n: usize) usize {
    var fba = std.heap.FixedBufferAllocator.init(&small);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    const a = arena.allocator();
    const s = a.alignedAlloc(u8, .@"8", 8) catch return 0;
    a.free(s);
    const t = a.alignedAlloc(u8, .@"8", n) catch return 1;
    return t.len + 1000 * arena.queryCapacity();
}
