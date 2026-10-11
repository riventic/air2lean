/// `rdtsc` is volatile: two executions return different counter values.
fn rdtscLow() u32 {
    return asm volatile ("rdtsc"
        : [ret] "={eax}" (-> u32),
        :
        : .{ .edx = true });
}

/// Natively false (the time-stamp counter advances between the two reads).
export fn sameTick() bool {
    const a = rdtscLow();
    const b = rdtscLow();
    return a == b;
}
