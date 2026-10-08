//! air2lean: one compilation never exports two different declarations under one identity
//! (docs/air-json.md §Identity). Each output file, named type and named global that the
//! exporter writes is claimed by the declaration that wrote it first. A claim by a different
//! declaration is a hard error: the process exits with status 1, so that a later translation
//! cannot silently use one declaration for the other.

const std = @import("std");
const Zcu = @import("../Zcu.zig");

const zv = @import("builtin").zig_version;

/// The kinds of exported identities. Each has its own namespace.
pub const Kind = enum(u8) { output, type, global };

/// The declaration that claimed an identity: its compilation and an ID that is unique there
/// (a `Nav.Index` or an `InternPool.Index`).
const Owner = struct { zcu: *const Zcu, id: u32 };

/// 0.16.0 has no `std.Thread.Mutex`. The lock is held only for a hash map update.
const Lock = if (zv.minor >= 16) struct {
    m: std.atomic.Mutex = .unlocked,
    fn lock(l: *@This()) void {
        while (!l.m.tryLock()) std.atomic.spinLoopHint();
    }
    fn unlock(l: *@This()) void {
        l.m.unlock();
    }
} else std.Thread.Mutex;

// The claims live as long as the process. Sub-compilations (compiler_rt, …) analyse on other
// threads, so the table is locked.
var lock: Lock = .{};
var arena: std.heap.ArenaAllocator = .init(std.heap.page_allocator);
var claims: std.StringHashMapUnmanaged(Owner) = .empty;

/// Record that `id` of `zcu` writes the identity `name` of `kind`. Exits the process if a
/// different declaration already wrote it.
pub fn claim(zcu: *const Zcu, kind: Kind, name: []const u8, id: u32) void {
    lock.lock();
    defer lock.unlock();
    const a = arena.allocator();
    const key = std.mem.concat(a, u8, &.{ &.{@intFromEnum(kind)}, name }) catch fatalOom();
    const gop = claims.getOrPut(a, key) catch fatalOom();
    if (!gop.found_existing) {
        gop.value_ptr.* = .{ .zcu = zcu, .id = id };
        return;
    }
    a.free(key);
    const previous = gop.value_ptr.*;
    if (previous.zcu == zcu and previous.id == id) return;
    std.log.err("air2lean: two different declarations export the {s} identity '{s}' " ++
        "(the exported AIR would describe only one of them; docs/air-json.md §Identity)", .{ @tagName(kind), name });
    std.process.exit(1);
}

fn fatalOom() noreturn {
    std.log.err("air2lean: out of memory while recording an exported identity", .{});
    std.process.exit(1);
}
