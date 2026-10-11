//! P08 end-to-end fixture: a real Zig loop that is exported by a patched compiler (I05 source
//! spans), translated, searched for a counterexample and replayed against the native program.
//! `sumUpTo` is the seeded off-by-one bug; `sumUpToOk` is the correct loop.

/// Intended contract: the sum of 0..n-1, that is n*(n-1)/2.
export fn sumUpTo(n: u32) u32 {
    var acc: u32 = 0;
    var i: u32 = 0;
    while (i <= n) : (i += 1) acc += i; // SPAN: off-by-one bound
    return acc;
}

export fn sumUpToOk(n: u32) u32 {
    var acc: u32 = 0;
    var i: u32 = 0;
    while (i < n) : (i += 1) acc += i; // SPAN: correct bound
    return acc;
}

/// Checked multiplication: a ReleaseSafe overflow panic for large operands.
export fn scale(a: u32, b: u32) u32 {
    return a * b; // SPAN: checked multiply
}
