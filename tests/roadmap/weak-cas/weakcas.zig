//! Qualified C11 weak-CAS source. Retry is bounded for native allowed-outcome checking.
pub fn weak(p: *u8, expected: u8, desired: u8) ?u8 {
    return @cmpxchgWeak(u8, p, expected, desired, .acq_rel, .acquire);
}
pub fn strong(p: *u8, expected: u8, desired: u8) ?u8 {
    return @cmpxchgStrong(u8, p, expected, desired, .acq_rel, .acquire);
}
pub fn weakBool(p: *bool, expected: bool, desired: bool) ?bool {
    return @cmpxchgWeak(bool, p, expected, desired, .acq_rel, .acquire);
}
pub fn retry(p: *u8, expected: u8, desired: u8, budget: u8) bool {
    var attempt: u8 = 0;
    while (attempt < budget) : (attempt += 1) {
        if (@cmpxchgWeak(u8, p, expected, desired, .acq_rel, .acquire)) |old| {
            if (old != expected) return false;
        } else return true;
    }
    return false;
}
comptime { _ = &weak; _ = &strong; _ = &weakBool; _ = &retry; }
