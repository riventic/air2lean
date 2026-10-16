//! F1 (soundness audit 2026-10-14): the standard library is `std` only with its reviewed sources.
//! `entry` reaches std code (the bounds check's panic handler), so its export names std's module.
pub fn entry(xs: []const u32, i: usize) u32 {
    return xs[i];
}

comptime {
    _ = &entry;
}
