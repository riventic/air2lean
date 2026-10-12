//! A02 probe (aarch64): the first aarch64 candidates for an instruction-semantics table, run
//! natively and compared with the Zig builtin each one realises. Not part of any proof.
const std = @import("std");

fn rev(x: u64) u64 {
    return asm ("rev %[ret], %[x]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
    );
}
fn clz(x: u64) u64 {
    return asm ("clz %[ret], %[x]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
    );
}
fn rbit(x: u64) u64 {
    return asm ("rbit %[ret], %[x]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
    );
}
/// Population count through NEON: `cnt` per byte, `addv` across bytes.
fn popcnt(x: u64) u64 {
    return asm ("fmov d0, %[x]\n\tcnt v0.8b, v0.8b\n\taddv b0, v0.8b\n\tfmov %[ret], d0"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
        : .{ .v0 = true });
}
/// `udiv` by zero is not a fault on aarch64: it yields zero.
fn udiv(a: u64, b: u64) u64 {
    return asm ("udiv %[ret], %[a], %[b]"
        : [ret] "=r" (-> u64),
        : [a] "r" (a),
          [b] "r" (b),
    );
}
fn cntvct() u64 {
    return asm volatile ("mrs %[ret], cntvct_el0"
        : [ret] "=r" (-> u64),
    );
}

pub fn main() void {
    const p = std.debug.print;
    var bad: u32 = 0;
    for ([_]u64{ 0, 1, 0x8000_0000_0000_0000, 0xffff_ffff_ffff_ffff, 0x00f0_0000_0000_0000, 0x0123_4567_89ab_cdef }) |x| {
        const ok = rev(x) == @byteSwap(x) and clz(x) == @clz(x) and rbit(x) == @bitReverse(x) and popcnt(x) == @popCount(x);
        if (!ok) bad += 1;
        p("x={x:0>16} rev={x:0>16} clz={} rbit={x:0>16} cnt={} agrees_with_builtins={}\n", .{ x, rev(x), clz(x), rbit(x), popcnt(x), ok });
    }
    p("udiv 100/0={} (no #DE on aarch64) udiv 100/7={}\n", .{ udiv(100, 0), udiv(100, 7) });
    const t0 = cntvct();
    const t1 = cntvct();
    p("cntvct_el0 t1>=t0={} (EL0-readable counter: an environment read)\n", .{t1 >= t0});
    p("mismatches={}\n", .{bad});
}
