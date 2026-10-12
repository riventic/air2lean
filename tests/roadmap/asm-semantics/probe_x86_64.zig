//! A02 probe (x86_64-linux): the instructions of the A01 allowlist run natively, to record what
//! the hand-written A03 interpretation (`tests/roadmap/asm-wrappers/Interp.lean`, AH-01) claims
//! and what the CPU does. Not part of any proof. Build and run: see README.md.
const std = @import("std");

fn lzcnt(x: u64) u64 {
    return asm ("lzcnt %[x], %[ret]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
        : .{ .cc = true });
}
fn popcnt(x: u64) u64 {
    return asm ("popcnt %[x], %[ret]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
    );
}
/// `bsr` is what `lzcnt`'s encoding (F3 0F BD) runs as on a CPU without LZCNT.
fn bsr(x: u64) u64 {
    return asm ("bsr %[x], %[ret]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
        : .{ .cc = true });
}
fn divl(a: u32, b: u32) [2]u32 {
    var q: u32 = undefined;
    var r: u32 = undefined;
    asm ("xorl %%edx, %%edx\n\tdivl %[b]"
        : [q] "={eax}" (q),
          [r] "=&{edx}" (r),
        : [a] "{eax}" (a),
          [b] "r" (b),
    );
    return .{ q, r };
}
fn tsc() u64 {
    return asm volatile ("rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"
        : [ret] "={rax}" (-> u64),
        :
        : .{ .rdx = true, .cc = true });
}
fn rdrand() struct { u64, u8 } {
    var v: u64 = undefined;
    var f: u8 = undefined;
    asm volatile ("rdrand %[v]\n\tsetc %[ok]"
        : [v] "=r" (v),
          [ok] "=r" (f),
        :
        : .{ .cc = true });
    return .{ v, f };
}
fn cpuid(leaf: u32, sub: u32) [4]u32 {
    var a: u32 = undefined;
    var b: u32 = undefined;
    var c: u32 = undefined;
    var d: u32 = undefined;
    asm volatile ("cpuid"
        : [a] "={eax}" (a),
          [b] "={ebx}" (b),
          [c] "={ecx}" (c),
          [d] "={edx}" (d),
        : [leaf] "{eax}" (leaf),
          [sub] "{ecx}" (sub),
    );
    return .{ a, b, c, d };
}

pub fn main() void {
    const p = std.debug.print;
    const l1 = cpuid(1, 0);
    const l7 = cpuid(7, 0);
    const lx = cpuid(0x80000001, 0);
    p("cpuid popcnt={} rdrand={} lzcnt(abm)={}\n", .{
        (l1[2] >> 23) & 1, (l1[2] >> 30) & 1, (lx[2] >> 5) & 1,
    });
    _ = l7;
    for ([_]u64{ 0, 1, 0x8000_0000_0000_0000, 0xffff_ffff_ffff_ffff, 0x00f0_0000_0000_0000 }) |x|
        p("x={x:0>16} lzcnt={} popcnt={}\n", .{ x, lzcnt(x), popcnt(x) });
    // The same encoding as a CPU without LZCNT would run it: bsr is undefined-flag, and the
    // destination for a zero source is unchanged (documented undefined, AMD: unchanged).
    p("bsr(1)={} bsr(2^63)={}\n", .{ bsr(1), bsr(0x8000_0000_0000_0000) });
    p("divl 100/7={any} divl 0xffffffff/1={any}\n", .{ divl(100, 7), divl(0xffff_ffff, 1) });
    const t0 = tsc();
    const t1 = tsc();
    // Rosetta's counter is coarse: two reads may be equal, so only the weak order is recorded.
    p("tsc t1>=t0={}\n", .{t1 >= t0});
    const r0 = rdrand();
    const r1 = rdrand();
    p("rdrand ok={}/{} equal={}\n", .{ r0[1], r1[1], r0[0] == r1[0] });
}
