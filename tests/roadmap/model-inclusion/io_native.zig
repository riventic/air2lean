//! W3 native leg for `std.Io`: one call of a `sync`/`iogroup` differential function or an
//! architecture-audit `std.Io` probe with a REAL `std.Io` implementation, printed to stderr as
//! the differential protocol's line (`{"ok":<u32>}` or `{"ok":{"err":"<Name>"}}`). A call that
//! never returns is a hang: `check.sh` runs each call under a timeout. Stock Zig 0.16.0:
//!   zig build-exe -OReleaseSafe -mcpu=baseline --dep sync --dep iogroup --dep io_probe \
//!     -Mroot=tests/roadmap/model-inclusion/io_native.zig -Msync=examples/sync/sync.zig \
//!     -Miogroup=examples/iogroup/iogroup.zig \
//!     -Mio_probe=tests/roadmap/architecture-audit/models/io_probe.zig
//! Usage: io_native threaded|single_threaded <function>
const std = @import("std");
const sync = @import("sync");
const iogroup = @import("iogroup");
const io_probe = @import("io_probe");

fn report(result: anytype) void {
    switch (@typeInfo(@TypeOf(result))) {
        .error_union => if (result) |v| {
            std.debug.print("{{\"ok\":{d}}}\n", .{v});
        } else |e| {
            std.debug.print("{{\"ok\":{{\"err\":\"{s}\"}}}}\n", .{@errorName(e)});
        },
        else => std.debug.print("{{\"ok\":{d}}}\n", .{result}),
    }
}

const functions = .{
    .{ "sync.mutexCounter", sync.mutexCounter },
    .{ "sync.handoff", sync.handoff },
    .{ "sync.semaphoreCounter", sync.semaphoreCounter },
    .{ "sync.rwLockRead", sync.rwLockRead },
    .{ "sync.rwLockSnapshotPair", sync.rwLockSnapshotPair },
    .{ "iogroup.groupCounter", iogroup.groupCounter },
    .{ "iogroup.groupConcurrent", iogroup.groupConcurrent },
    .{ "io_probe.cancelProbe", io_probe.cancelProbe },
    .{ "io_probe.handoffProbe", io_probe.handoffProbe },
};

pub fn main(init: std.process.Init.Minimal) !void {
    if (init.args.vector.len != 3) return error.Usage;
    const kind = std.mem.span(init.args.vector[1]);
    const name = std.mem.span(init.args.vector[2]);
    var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
    defer threaded.deinit();
    const io = if (std.mem.eql(u8, kind, "threaded"))
        threaded.io()
    else if (std.mem.eql(u8, kind, "single_threaded"))
        std.Io.Threaded.global_single_threaded.io()
    else
        return error.Usage;
    inline for (functions) |entry| {
        if (std.mem.eql(u8, name, entry[0])) return report(entry[1](io));
    }
    return error.Usage;
}
