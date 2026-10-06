const std = @import("std");
const source = @import("source.zig");

const Mode = enum { in_place, moved, failed };

/// Three fixed backing buffers, each with capacity 16. Slots never reuse addresses.
/// Logical lengths define live allocations; byte-only/alignment-1 policy is explicit.
const BoundedAllocator = struct {
    mode: Mode,
    storage: [3][16]u8 = undefined,
    lengths: [3]usize = .{ 0, 0, 0 },
    live: [3]bool = .{ false, false, false },
    next: usize = 0,
    remaps: usize = 0,
    old_live_after_remap: bool = false,
    prefix_preserved: bool = false,
    frame_preserved: bool = false,

    fn allocator(self: *BoundedAllocator) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{ .alloc = alloc, .resize = resize, .remap = remap, .free = free } };
    }
    fn slot(self: *BoundedAllocator, memory: []u8) ?usize {
        for (0..self.next) |i| {
            if (self.live[i] and self.storage[i][0..].ptr == memory.ptr and self.lengths[i] == memory.len)
                return i;
        }
        return null;
    }
    fn alloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, _: usize) ?[*]u8 {
        const self: *BoundedAllocator = @ptrCast(@alignCast(ctx));
        if (len == 0 or len > 16 or alignment.toByteUnits() != 1 or self.next == 3) return null;
        const i = self.next;
        self.next += 1;
        self.lengths[i] = len;
        self.live[i] = true;
        @memset(self.storage[i][0..], undefined);
        return self.storage[i][0..].ptr;
    }
    fn resize(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) bool { return false; }
    fn remap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, _: usize) ?[*]u8 {
        const self: *BoundedAllocator = @ptrCast(@alignCast(ctx));
        const i = self.slot(memory) orelse @panic("not a live whole allocation");
        if (alignment.toByteUnits() != 1) @panic("byte alignment required");
        self.remaps += 1;
        const before = self.storage[i];
        const frame = self.storage[0][0];
        var result: ?[*]u8 = null;
        if (new_len != 0 and new_len <= 16) {
            switch (self.mode) {
                .failed => {},
                .in_place => {
                    // Growth is restricted to the latest allocated slot, matching the proposed model.
                    if (new_len <= memory.len or i + 1 == self.next) {
                        if (new_len > memory.len) @memset(self.storage[i][memory.len..new_len], undefined);
                        self.lengths[i] = new_len;
                        result = self.storage[i][0..].ptr;
                    }
                },
                .moved => {
                    if (self.next < 3) {
                        const j = self.next;
                        self.next += 1;
                        @memset(self.storage[j][0..], undefined);
                        @memcpy(self.storage[j][0..@min(memory.len, new_len)], memory[0..@min(memory.len, new_len)]);
                        self.lengths[j] = new_len;
                        self.live[j] = true;
                        self.live[i] = false;
                        result = self.storage[j][0..].ptr;
                    }
                },
            }
        }
        self.old_live_after_remap = self.live[i];
        self.prefix_preserved = if (result) |p|
            std.mem.eql(u8, p[0..@min(memory.len, new_len)], before[0..@min(memory.len, new_len)])
        else self.live[i] and self.lengths[i] == memory.len and std.mem.eql(u8, memory, before[0..memory.len]);
        self.frame_preserved = self.live[0] and self.lengths[0] == 1 and self.storage[0][0] == frame;
        return result;
    }
    fn free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, _: usize) void {
        const self: *BoundedAllocator = @ptrCast(@alignCast(ctx));
        const i = self.slot(memory) orelse @panic("free requires a live whole allocation");
        if (alignment.toByteUnits() != 1) @panic("byte alignment required");
        self.live[i] = false;
    }
};

pub fn main() !void {
    for ([_]Mode{ .in_place, .moved, .failed }, [_]u32{ 101, 201, 301 }) |mode, expected| {
        var a: BoundedAllocator = .{ .mode = mode };
        const result = try source.exercise(a.allocator());
        if (result != expected or a.remaps != 1 or !a.prefix_preserved or !a.frame_preserved or
            a.old_live_after_remap != (mode != .moved) or a.live[0] or a.live[1] or a.live[2])
            return error.RemapOrCleanupMismatch;
        std.debug.print("{{\"mode\":\"{s}\",\"result\":{d},\"prefix_preserved\":true,\"frame_preserved\":true,\"old_live_after_remap\":{s},\"live_after_cleanup\":0}}\n",
            .{ @tagName(mode), result, if (a.old_live_after_remap) "true" else "false" });
    }
}
