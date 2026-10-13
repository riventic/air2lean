const std = @import("std");

var buffer: [256]u8 = undefined;

/// After an allocation that fails (the child is out of memory), the arena's first node keeps
/// `end_index > buf.len`; `free` then computes `buf_ptr + cur_end_index` past the node.
pub export fn repro(n: usize) bool {
    var fba = std.heap.FixedBufferAllocator.init(&buffer);
    var arena = std.heap.ArenaAllocator.init(fba.allocator());
    const a = arena.allocator();
    const s = a.alloc(u8, n) catch return false;
    _ = a.alloc(u8, 4096) catch {};
    a.free(s);
    return true;
}

pub fn main() void {
    std.debug.print("{}\n", .{repro(8)});
}
