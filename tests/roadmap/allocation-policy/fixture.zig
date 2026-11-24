const std = @import("std");
const common = @import("common");

const Rule = common.TestAllocator.OracleRule;

fn attempt(a: std.mem.Allocator, size: usize) bool {
    const bytes = a.alloc(u8, size) catch return false;
    defer a.free(bytes);
    return true;
}

/// One request per size under the policy of `policy`. Each success is freed at once, or with
/// `hold` after the last request, so that the live bytes count against a budget; a held run
/// also reports the live bytes before the frees.
fn checkPolicy(name: []const u8, policy: common.TestAllocator, hold: bool, sizes: []const usize,
    expected: []const bool) !void {
    var ta = policy;
    defer ta.live.deinit(std.heap.page_allocator);
    const a = ta.allocator();
    var held: [8]?[]u8 = @splat(null);
    std.debug.print("{{\"case\":\"{s}\",\"outcomes\":[", .{name});
    for (sizes, expected, 0..) |size, want, i| {
        const ok = if (hold) blk: {
            held[i] = a.alloc(u8, size) catch null;
            break :blk held[i] != null;
        } else attempt(a, size);
        if (ok != want or (!hold and ta.live.items.len != 0)) return error.PolicyOrCleanupMismatch;
        if (i != 0) std.debug.print(",", .{});
        std.debug.print("{d}", .{@intFromBool(ok)});
    }
    if (ta.count != sizes.len) return error.AttemptCountMismatch;
    std.debug.print("],\"attempts\":{d}", .{ta.count});
    if (hold) {
        std.debug.print(",\"held\":{d}", .{ta.liveBytes()});
        for (held) |block| if (block) |b| a.free(b);
        if (ta.live.items.len != 0) return error.PolicyOrCleanupMismatch;
    }
    std.debug.print(",\"live\":0}}\n", .{});
}

fn checkCase(name: []const u8, cap: usize, failures: []const usize, fail_at: ?usize,
    sizes: []const usize, expected: []const bool) !void {
    try checkPolicy(name, .{ .request_cap = cap, .failures = failures, .fail_at = fail_at }, false, sizes, expected);
}

fn checkJsonPolicy() !void {
    const gpa = std.heap.page_allocator;
    var parsed = try std.json.parseFromSlice(std.json.Value, gpa,
        "{\"fail_at\":1,\"failures\":[0,2],\"max_bytes\":64,\"budget\":40,\"oracle\":[" ++
        "{\"attempt_min\":3,\"attempt_max\":5,\"attempt_mod\":2,\"attempt_rem\":1,\"bytes_min\":9,\"bytes_max\":16},{}]}", .{});
    defer parsed.deinit();
    var policy = try common.TestAllocator.fromJson(gpa, parsed.value);
    defer policy.deinitPolicy(gpa);
    if (policy.fail_at != 1 or policy.request_cap != 64 or policy.failures.len != 2 or
        policy.failures[0] != 0 or policy.failures[1] != 2) return error.PolicyDecodeMismatch;
    if (policy.budget != 40 or policy.oracle.len != 2 or
        !std.meta.eql(policy.oracle[0], Rule{ .attempt_min = 3, .attempt_max = 5, .attempt_mod = 2,
            .attempt_rem = 1, .bytes_min = 9, .bytes_max = 16 }) or
        !std.meta.eql(policy.oracle[1], Rule{})) return error.PolicyDecodeMismatch;
    for ([_][]const u8{ "-1", "{\"failures\":[-1]}", "{\"max_bytes\":-1}",
        "{\"failures\":false}", "[]", "{\"budget\":-1}", "{\"oracle\":{}}", "{\"oracle\":[3]}",
        "{\"oracle\":[{\"attempt_mod\":0}]}", "{\"oracle\":[{\"bytes\":1}]}",
        "{\"failures\":[0],\"oracle\":[{\"bytes_min\":-1}]}", "{\"budgets\":1}" }) |input| {
        var invalid = try std.json.parseFromSlice(std.json.Value, gpa, input, .{});
        defer invalid.deinit();
        if (common.TestAllocator.fromJson(gpa, invalid.value)) |accepted| {
            var unexpected = accepted;
            unexpected.deinitPolicy(gpa);
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
    // The failure oracle over (attempt, bytes) and the live-byte budget. Check.lean states each
    // oracle as a Lean function, not as rules.
    try checkPolicy("oracle-even-attempts", .{ .oracle = &.{.{ .attempt_mod = 2 }} }, false,
        &.{8, 8, 8, 8, 8, 8}, &.{false, true, false, true, false, true});
    try checkPolicy("oracle-by-size", .{ .oracle = &.{.{ .bytes_min = 17 }} }, false,
        &.{8, 32, 16, 17}, &.{true, false, true, false});
    try checkPolicy("oracle-attempt-and-size", .{ .oracle = &.{.{ .attempt_min = 2, .bytes_max = 8 }} }, false,
        &.{8, 8, 8, 16, 4}, &.{true, true, false, true, false});
    try checkPolicy("oracle-two-rules", .{ .oracle = &.{ .{ .attempt_min = 1, .attempt_max = 1 }, .{ .bytes_min = 64 } } },
        false, &.{8, 8, 64, 8}, &.{true, false, false, true});
    try checkPolicy("oracle-all", .{ .oracle = &.{.{}} }, false, &.{8, 8, 8}, &.{false, false, false});
    try checkPolicy("oracle-with-list-and-cap", .{ .request_cap = 32, .failures = &.{1}, .oracle = &.{.{ .attempt_mod = 3, .attempt_rem = 2 }} },
        false, &.{8, 8, 8, 33, 32, 8}, &.{true, false, false, false, true, false});
    try checkPolicy("budget-held", .{ .budget = 20 }, true, &.{8, 8, 8, 4, 1}, &.{true, true, false, true, false});
    try checkPolicy("budget-released", .{ .budget = 8 }, false, &.{8, 8, 9, 8}, &.{true, true, false, true});
    try checkPolicy("budget-zero", .{ .budget = 0 }, false, &.{1, 8}, &.{false, false});
    try checkPolicy("budget-and-oracle", .{ .budget = 16, .oracle = &.{.{ .attempt_max = 0 }} }, true,
        &.{8, 8, 8, 8}, &.{false, true, true, false});
}
