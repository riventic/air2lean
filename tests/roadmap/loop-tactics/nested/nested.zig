//! P03 nested loops: an inner counter loop inside the body of an outer counter loop.

/// Adds one to `acc.*` for every pair `j < i < n`, so `acc.*` grows by `n * (n - 1) / 2`.
/// The add is checked: it panics if `acc.*` overflows.
export fn pairs(acc: *u64, n: u32) void {
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        var j: u32 = 0;
        while (j < i) : (j += 1) acc.* += 1;
    }
}
