//! Forces the eager memory ABI of a zero-length over-aligned payload into exported AIR.
const E = error{Bad};
export fn zeroArray(x: *E![0]u64) bool {
    return if (x.*) |_| true else |_| false;
}
