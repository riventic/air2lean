//! Shifts of an integer whose width is not a power of two (docs/illegal-behavior.md row 14),
//! with Sema's shift-amount check on some paths only. A shift is total in the model only where
//! it runs after the check of its own amount (`FCtx.shiftCountGuarded`); every other one checks
//! the amount itself. `check.sh` runs `ShiftCases.lean` on each version's translation.

/// The first shift has no check (safety is off in its scope); the second one has Sema's.
pub fn mixed(x: u24, c: u5, flag: bool) u24 {
    if (flag) {
        @setRuntimeSafety(false);
        return x << c;
    }
    return x << c;
}

/// As `mixed`, for `>>` on a signed operand.
pub fn mixedShr(x: i24, c: u5, flag: bool) i24 {
    if (flag) {
        @setRuntimeSafety(false);
        return x >> c;
    }
    return x >> c;
}

/// The checked shift comes first: its check does not guard the later unchecked one.
pub fn checkedFirst(x: u24, c: u5, flag: bool) u24 {
    const y = x << c;
    if (flag) {
        @setRuntimeSafety(false);
        return y << c;
    }
    return y;
}

/// The amounts differ: the check of `c` does not guard the shift by `d`.
pub fn otherCount(x: u24, c: u5, d: u5) u24 {
    const y = x << c;
    {
        @setRuntimeSafety(false);
        return y << d;
    }
}

/// Every shift has Sema's check.
pub fn safe(x: u24, c: u5) u24 {
    return (x << c) >> c;
}

/// No shift has it.
pub fn unsafeOnly(x: u24, c: u5) u24 {
    @setRuntimeSafety(false);
    return x << c;
}

comptime {
    _ = &mixed;
    _ = &mixedShr;
    _ = &checkedFirst;
    _ = &otherCount;
    _ = &safe;
    _ = &unsafeOnly;
}
