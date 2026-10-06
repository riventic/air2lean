const std = @import("std");
const fixture = @import("error_storage.zig");
pub fn main() void {
    const values = [_]fixture.Failure{error.Alpha, error.Beta, error.Gamma};
    for (values) |name| {
        var slots = [_]?fixture.Failure{error.Gamma, null, error.Beta};
        const got = fixture.overwrite(&slots, name);
        var e: fixture.Failure = error.Alpha;
        const stored = fixture.writeError(&e, name);
        var optional: ?fixture.Failure = null;
        const payload = fixture.writePayload(&optional, name);
        const global = fixture.globalRoundtrip(name);
        const propagation = if (fixture.propagate(&e)) |_| false else |err| err == name;
        var outer: ??fixture.Failure = null;
        const inner_null: ?fixture.Failure = null;
        const nested = fixture.nestedOuter(&outer, inner_null);
        const nested_null_ok = nested != null and nested.? == null and outer != null and outer.? == null;
        const nested_error = fixture.nestedOuter(&outer, @as(?fixture.Failure, name));
        const nested_ok = nested_null_ok and nested_error != null and nested_error.? == name and outer != null and outer.? == name;
        var union_cell: fixture.Failure!fixture.ErrorPayload = error.Gamma;
        const union_ok = if (fixture.payloadUnion(&union_cell, name, false)) |value|
            value.code == name and (if (union_cell) |stored_value| stored_value.code == name else |_| false)
        else |_| false;
        const union_err = if (fixture.payloadUnion(&union_cell, name, true)) |_| false
        else |err| err == name and (if (union_cell) |_| false else |stored_err| stored_err == name);
        std.debug.print("{s} {d} {d} {d} {d} {d} {d} {d} {d} {d}\n", .{
            @errorName(name), @intFromBool(got == name),
            @intFromBool(slots[0] == null and slots[2] == error.Beta),
            @intFromBool(stored == name and fixture.readError(&e) == name),
            @intFromBool(payload == error.Gamma and optional == error.Gamma),
            @intFromBool(global == name and fixture.global_status.guard == 37 and fixture.global_status.pending == name and fixture.global_status.last == name and fixture.statuses[0] == null and fixture.statuses[2] == error.Beta),
            @intFromBool(propagation), @intFromBool(nested_ok), @intFromBool(union_ok), @intFromBool(union_err),
        });
    }
}
