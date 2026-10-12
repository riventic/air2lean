//! Native probe of `tls_pointers.zig` (stock Zig 0.15.2-0.17.0; 0.14.1 is rejected by the
//! translator). `ModelTlsPointers.lean` prints the same lines from the translation under 16
//! schedules. `leakedSlot` is not called: natively it reads a dead thread's instance (illegal
//! behaviour), which the model reports as `.illegal`.
const std = @import("std");
const tp = @import("tls_pointers.zig");

pub fn main() void {
    std.debug.print("perThread {d}\n", .{tp.perThread() catch 0});
    std.debug.print("mainOnly 3 {d}\n", .{tp.mainOnly(3)});
    std.debug.print("mainOnly 100 {d}\n", .{tp.mainOnly(100)});
    std.debug.print("perThread {d}\n", .{tp.perThread() catch 0});
}
