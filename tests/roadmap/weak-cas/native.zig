const std = @import("std");
const source = @import("weakcas.zig");
test "weak matching read has only permitted source outcomes" {
    var matching_failures: usize = 0;
    var successes: usize = 0;
    for (0..64) |_| {
        var cell: u8 = 42;
        if (source.weak(&cell, 42, 7)) |old| {
            try std.testing.expectEqual(@as(u8, 42), old);
            try std.testing.expectEqual(@as(u8, 42), cell);
            matching_failures += 1;
        } else {
            try std.testing.expectEqual(@as(u8, 7), cell);
            successes += 1;
        }
        cell = 42;
        try std.testing.expectEqual(@as(?u8, 42), source.weak(&cell, 99, 7));
        try std.testing.expectEqual(@as(u8, 42), cell);
        cell = 42;
        try std.testing.expectEqual(@as(?u8, null), source.strong(&cell, 42, 7));
        try std.testing.expectEqual(@as(u8, 7), cell);
        cell = 42;
        const done = source.retry(&cell, 42, 7, 3);
        try std.testing.expectEqual(@as(u8, if (done) 7 else 42), cell);
        var bit = false;
        if (source.weakBool(&bit, false, true)) |old| {
            try std.testing.expect(!old and !bit);
        } else try std.testing.expect(bit);
    }
    std.debug.print("C11 native allowed outcomes: successes={d}, matching_failures={d}\n", .{ successes, matching_failures });
}
