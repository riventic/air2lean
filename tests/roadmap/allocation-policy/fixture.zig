const std = @import("std");
const common = @import("common");

fn attempt(a: std.mem.Allocator, size: usize) bool {
    const bytes = a.alloc(u8, size) catch return false;
    defer a.free(bytes);
    return true;
}

fn checkCase(name: []const u8, cap: usize, failures: []const usize, fail_at: ?usize,
    sizes: []const usize, expected: []const bool) !void {
    var ta: common.TestAllocator = .{ .request_cap = cap, .failures = failures, .fail_at = fail_at };
    defer ta.live.deinit(std.heap.page_allocator);
    std.debug.print("{{\"case\":\"{s}\",\"outcomes\":[", .{name});
    for (sizes, expected, 0..) |size, want, i| {
        const ok = attempt(ta.allocator(), size);
        if (ok != want or ta.live.items.len != 0) return error.PolicyOrCleanupMismatch;
        if (i != 0) std.debug.print(",", .{});
        std.debug.print("{d}", .{@intFromBool(ok)});
    }
    if (ta.count != sizes.len) return error.AttemptCountMismatch;
    std.debug.print("],\"attempts\":{d},\"live\":0}}\n", .{ta.count});
}

fn checkJsonPolicy() !void {
    const gpa = std.heap.page_allocator;
    var parsed = try std.json.parseFromSlice(std.json.Value, gpa,
        "{\"fail_at\":1,\"failures\":[0,2],\"max_bytes\":64}", .{});
    defer parsed.deinit();
    const policy = try common.TestAllocator.fromJson(gpa, parsed.value);
    defer gpa.free(policy.failures);
    if (policy.fail_at != 1 or policy.request_cap != 64 or policy.failures.len != 2 or
        policy.failures[0] != 0 or policy.failures[1] != 2) return error.PolicyDecodeMismatch;
    for ([_][]const u8{ "-1", "{\"failures\":[-1]}", "{\"max_bytes\":-1}",
        "{\"failures\":false}", "[]" }) |input| {
        var invalid = try std.json.parseFromSlice(std.json.Value, gpa, input, .{});
        defer invalid.deinit();
        if (common.TestAllocator.fromJson(gpa, invalid.value)) |unexpected| {
            if (unexpected.failures.len != 0) gpa.free(unexpected.failures);
            return error.AcceptedInvalidPolicy;
        } else |err| {
            if (err != error.InvalidAllocatorPolicy) return err;
        }
    }
}

pub fn main() !void {
    try checkJsonPolicy();
    const cap = common.TestAllocator.max_alloc_bytes;
    try checkCase("legacy-success", cap, &.{}, null, &.{8, 8}, &.{true, true});
    try checkCase("legacy-failure", cap, &.{}, 0, &.{8, 8}, &.{false, true});
    try checkCase("several-failures", cap, &.{0, 2}, null, &.{8, 8, 8, 8}, &.{false, true, false, true});
    try checkCase("combined", cap, &.{2}, 0, &.{8, 8, 8}, &.{false, true, false});
    try checkCase("duplicate-indices", cap, &.{0, 0, 2}, null, &.{8, 8, 8}, &.{false, true, false});
    try checkCase("all-fail", cap, &.{0, 1, 2}, null, &.{8, 8, 8}, &.{false, false, false});
    try checkCase("cap-boundary", 32, &.{}, null, &.{32, 33, 16}, &.{true, false, true});
    try checkCase("raised-cap", 2 * cap, &.{}, null, &.{cap + 1}, &.{true});
    try checkCase("default-cap", cap, &.{}, null, &.{cap + 1}, &.{false});
    var zero: common.TestAllocator = .{ .request_cap = 0, .failures = &.{0} };
    defer zero.live.deinit(std.heap.page_allocator);
    if (!attempt(zero.allocator(), 0) or zero.count != 0 or zero.live.items.len != 0)
        return error.ZeroSizeConsumedPolicy;
    std.debug.print("{{\"case\":\"zero\",\"outcomes\":[1],\"attempts\":0,\"live\":0}}\n", .{});
}
