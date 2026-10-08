// MM-3: Zig 0.16 lowers `ptr_add`/`ptr_sub`/field pointers to `getelementptr inbounds`
// (src/codegen/llvm/FuncGen.zig `ptraddScaled`). A pointer outside its allocation (beyond one
// past the end) is LLVM poison, and LLVM folds comparisons on it. The model's `Ptr.add` accepts
// any offset and compares concrete addresses, with no `.illegal`, so it answers differently.
const std = @import("std");

pub noinline fn oobCompare(k: usize) bool {
    var a: [4]u8 = .{ 1, 2, 3, 4 };
    const p: [*]u8 = &a;
    p[0] = 9;
    const q = p + k;
    return @intFromPtr(q) > @intFromPtr(p);
}

pub noinline fn oobPtrCompare(k: usize) bool {
    var a: [4]u8 = .{ 1, 2, 3, 4 };
    const p: [*]u8 = &a;
    p[0] = 9;
    const q = p + k;
    return @intFromPtr(q) > @intFromPtr(p) and q != p;
}

pub fn main() void {
    const big: usize = @as(usize, 1) << 63;
    std.debug.print("oobCompare(1) {d}\n", .{@intFromBool(oobCompare(1))});
    std.debug.print("oobCompare(2^63) {d}\n", .{@intFromBool(oobCompare(big))});
    std.debug.print("oobPtrCompare(2^63) {d}\n", .{@intFromBool(oobPtrCompare(big))});
}
