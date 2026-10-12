//! Native probe of `extern_storage.zig` (stock Zig 0.14.1-0.17.0), linked with
//! `provider_extern_storage.c`. `ModelExternStorage.lean` prints the same lines from the
//! translation with the provider's values as `ext`.
const std = @import("std");
const es = @import("extern_storage.zig");

pub fn main() void {
    std.debug.print("sumList {d}\n", .{es.sumList()});
    std.debug.print("nameLen {d}\n", .{es.nameLen()});
    std.debug.print("slotValue {d}\n", .{es.slotValue()});
    std.debug.print("pushLocal {d}\n", .{es.pushLocal()});
    std.debug.print("counter {d}\n", .{es.counter()});
    std.debug.print("slotValue {d}\n", .{es.slotValue()});
    std.debug.print("sumList {d}\n", .{es.sumList()});
}
