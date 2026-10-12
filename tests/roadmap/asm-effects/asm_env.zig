//! A01 fixture (x86_64, Zig 0.15.2+ clobber syntax): environment reads, a memory input and
//! memory-region contracts (docs/generated-code.md §Inline asm, Air2Lean/AsmAllowlist.lean).

/// Two time-stamp counter reads: two environment reads, never one repeatable value (ASM-05).
pub fn elapsed() u64 {
    const t0 = ticks();
    const t1 = ticks();
    return t1 -% t0;
}

pub fn ticks() u64 {
    return asm volatile ("rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"
        : [ret] "={rax}" (-> u64),
        :
        : .{ .rdx = true, .cc = true });
}

/// A hardware random number (ASM-05).
pub fn random() u64 {
    return asm volatile ("rdrand %[ret]"
        : [ret] "=r" (-> u64),
        :
        : .{ .cc = true });
}

/// rdrand with its success flag: two lvalue outputs, both environment reads.
pub fn rand64(ok: *u8) u64 {
    var v: u64 = undefined;
    var f: u8 = undefined;
    asm volatile ("rdrand %[v]\n\tsetc %[ok]"
        : [v] "=r" (v),
          [ok] "=r" (f),
        :
        : .{ .cc = true });
    ok.* = f;
    return v;
}

/// A memory input operand: the compiler's private copy of the value.
pub fn loadm(p: *const u64) u64 {
    return asm ("movq %[x], %[ret]"
        : [ret] "=r" (-> u64),
        : [x] "m" (p.*),
    );
}

/// `rep stosb`: writes `n` bytes at `dst` (memory-region contract, ASM-06).
pub fn fill(dst: [*]u8, n: usize, b: u8) void {
    var d = dst;
    var c = n;
    asm volatile ("rep stosb"
        : [d] "+{rdi}" (d),
          [c] "+{rcx}" (c),
        : [b] "{al}" (b),
        : .{ .memory = true });
}

/// `rep movsb`: reads `n` bytes at `src`, writes `n` bytes at `dst` (ASM-06).
pub fn copy(dst: [*]u8, src: [*]const u8, n: usize) void {
    var d = dst;
    var s = src;
    var c = n;
    asm volatile ("rep movsb"
        : [d] "+{rdi}" (d),
          [s] "+{rsi}" (s),
          [c] "+{rcx}" (c),
        :
        : .{ .memory = true });
}

comptime {
    _ = &elapsed;
    _ = &random;
    _ = &rand64;
    _ = &loadm;
    _ = &fill;
    _ = &copy;
}
