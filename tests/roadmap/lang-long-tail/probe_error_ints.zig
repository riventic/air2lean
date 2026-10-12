//! Native probe of `error_ints.zig` (stock Zig 0.14.1-0.17.0), and the root of its AIR export:
//! the error numbering is per compilation, so `export.sh` exports this compilation
//! (`error_ints.root`), with the same flags as the native build. `ModelErrorInts.lean` prints the
//! same lines from the translation and the exported numbering.
const std = @import("std");
const ei = @import("error_ints.zig");

pub fn main() void {
    inline for (.{ error.Alpha, error.Beta, error.Gamma }) |e| {
        const c = ei.code(e);
        std.debug.print("code {s} {d} {s} {} {}\n", .{ @errorName(e), c, ei.nameOf(c), ei.roundTrip(e), ei.viaMemory(e) });
    }
    var c: ei.Code = 1;
    while (c <= 8) : (c += 1) std.debug.print("nameOf {d} {s}\n", .{ c, ei.nameOf(c) });
}
