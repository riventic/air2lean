//! Native witness for `CheckCtx.checkMulAdd`: one `f32` `@mulAdd` whose result depends on how
//! the CPU's features make the backend compute it. `native.sh` builds it for x86_64-linux at
//! `-mcpu=baseline` (compiler_rt's `fmaf`) and `-mcpu=haswell` (`vfmadd…`) and prints both.
//! Up to Zig 0.16.0 `fmaf` rounds twice and returns `0x3f800000` where the instruction returns
//! the correctly rounded `0x3f800001` (docs/floats.md, group B).
const std = @import("std");

export fn fma32(a: f32, b: f32, c: f32) f32 {
    return @mulAdd(f32, a, b, c);
}

var inputs: [3]u32 = .{ 0x3f800001, 0x3f7fffff, 0x28000001 };

pub fn main() void {
    // Volatile: the operands are not constants to the optimizer.
    const in: *volatile [3]u32 = &inputs;
    const r = fma32(@bitCast(in[0]), @bitCast(in[1]), @bitCast(in[2]));
    std.debug.print("fma32 0x{x:0>8}\n", .{@as(u32, @bitCast(r))});
}
