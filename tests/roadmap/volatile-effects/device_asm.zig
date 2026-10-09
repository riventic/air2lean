//! L13 inline-asm effect fixture (docs/volatile-effects.md §Inline asm), x86_64 only, Zig
//! 0.15.2/0.16.0 clobber syntax. None of these asm is on the reviewed allowlist, so the default
//! translation rejects every function with ASM_VOLATILE_EFFECT. With
//! `--device-contract tests/roadmap/volatile-effects/tsc.json` only `elapsed` is accepted: its
//! two `rdtsc` are two device events (`Zig.vasm`), never one repeatable value.

/// Two reads of the time-stamp counter.
pub fn elapsed() u64 {
    const t0 = asm volatile ("rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"
        : [ret] "={rax}" (-> u64),
        :
        : .{ .rdx = true, .cc = true });
    const t1 = asm volatile ("rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"
        : [ret] "={rax}" (-> u64),
        :
        : .{ .rdx = true, .cc = true });
    return t1 -% t0;
}

/// A hardware random number: a nondeterministic output.
pub fn random() u64 {
    return asm volatile ("rdrand %[ret]"
        : [ret] "=r" (-> u64),
        :
        : .{ .cc = true });
}

/// An output-less asm: an effect with no value (a full memory fence).
pub fn fence() void {
    asm volatile ("mfence");
}

/// A compiler barrier: a `memory` clobber, also outside the device contract (DEV-01).
pub fn barrier() void {
    asm volatile (""
        :
        :
        : .{ .memory = true });
}

/// The counter without `volatile`: still not input-determined, so not a repeatable opaque.
pub fn ticksPlain() u64 {
    return asm ("rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"
        : [ret] "={rax}" (-> u64),
        :
        : .{ .rdx = true, .cc = true });
}

comptime {
    _ = &elapsed;
    _ = &random;
    _ = &fence;
    _ = &barrier;
    _ = &ticksPlain;
}
