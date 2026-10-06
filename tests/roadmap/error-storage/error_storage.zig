const std = @import("std");
pub const Failure = error{Alpha, Beta, Gamma};
pub const ErrorPayload = struct { code: Failure };
pub const Status = struct { guard: u16, pending: ?Failure, last: Failure };
pub var statuses = [_]?Failure{null, error.Alpha, error.Beta};
pub var global_status: Status = .{ .guard = 37, .pending = null, .last = error.Gamma };

pub fn overwrite(slots: *[3]?Failure, value: Failure) ?Failure {
    slots[1] = value;
    slots[0] = null;
    return slots[1];
}
pub fn readError(cell: *Failure) Failure { return cell.*; }
pub fn writeError(cell: *Failure, value: Failure) Failure { cell.* = value; return cell.*; }
pub fn writePayload(slot: *?Failure, value: Failure) Failure {
    slot.* = value;
    const payload = &(slot.*.?);
    payload.* = error.Gamma;
    return payload.*;
}
pub fn globalRoundtrip(value: Failure) ?Failure {
    global_status.last = value;
    global_status.pending = value;
    statuses[1] = global_status.last;
    return statuses[1];
}
pub fn propagate(cell: *Failure) Failure!u8 { return cell.*; }
pub fn nestedOuter(slot: *??Failure, value: ?Failure) ??Failure { slot.* = value; return slot.*; }
pub fn payloadUnion(cell: *Failure!ErrorPayload, value: Failure, fail: bool) Failure!ErrorPayload {
    if (fail) cell.* = value else cell.* = .{ .code = value };
    return cell.*;
}
comptime {
    _ = &overwrite; _ = &readError; _ = &writeError; _ = &writePayload;
    _ = &globalRoundtrip; _ = &propagate; _ = &nestedOuter; _ = &payloadUnion;
}
test "standalone, optional, array and aggregate error identity" {
    var slots = [_]?Failure{error.Gamma, null, error.Beta};
    try std.testing.expectEqual(@as(?Failure, error.Alpha), overwrite(&slots, error.Alpha));
    try std.testing.expect(slots[0] == null);
    try std.testing.expectEqual(@as(?Failure, error.Beta), slots[2]);
    var cell: Failure = error.Alpha;
    try std.testing.expectEqual(error.Beta, writeError(&cell, error.Beta));
    try std.testing.expectEqual(error.Beta, readError(&cell));
    var optional: ?Failure = null;
    try std.testing.expectEqual(error.Gamma, writePayload(&optional, error.Alpha));
    try std.testing.expectEqual(@as(?Failure, error.Gamma), optional);
    try std.testing.expectEqual(@as(?Failure, error.Beta), globalRoundtrip(error.Beta));
    try std.testing.expectEqual(@as(u16, 37), global_status.guard);
    try std.testing.expectError(error.Beta, propagate(&cell));
    var outer: ??Failure = null;
    const middle: ?Failure = null;
    const some_null = nestedOuter(&outer, middle);
    try std.testing.expect(some_null != null);
    try std.testing.expect(some_null.? == null);
    const some_error = nestedOuter(&outer, @as(?Failure, error.Alpha));
    try std.testing.expectEqual(error.Alpha, some_error.?.?);
    var union_cell: Failure!ErrorPayload = error.Gamma;
    const success = try payloadUnion(&union_cell, error.Alpha, false);
    try std.testing.expectEqual(error.Alpha, success.code);
    try std.testing.expectEqual(error.Alpha, (try union_cell).code);
    try std.testing.expectError(error.Beta, payloadUnion(&union_cell, error.Beta, true));
    try std.testing.expectError(error.Beta, union_cell);
}
