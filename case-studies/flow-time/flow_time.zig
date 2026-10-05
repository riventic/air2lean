//! Monomorphic entry points for Flow's original timestamp implementation.
//! Bind `flow_time_original` to the production file; this wrapper has no arithmetic.
const original = @import("flow_time_original");

pub fn timestamp32(base: u32, duration: u32) error{TimeOverflow}!u32 {
    return original.addDuration(base, duration);
}

pub fn timestamp64(base: u64, duration: u64) error{TimeOverflow}!u64 {
    return original.addDuration(base, duration);
}

comptime {
    _ = &timestamp32;
    _ = &timestamp64;
}
