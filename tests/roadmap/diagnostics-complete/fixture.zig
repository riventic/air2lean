//! I05 source-span evidence: independent blockers in exported functions, one of them inside an
//! inlined callee. Exported only by an explicitly supplied patched compiler; never executed.

inline fn readInline(p: *volatile u32) u32 {
    return p.*; // SPAN: inlined volatile load
}

export fn volatileTwice(p: *volatile u32) u32 {
    const a = p.*; // SPAN: direct volatile load
    const b = readInline(p);
    return a +% b;
}

export fn unorderedLoad(p: *u32) u32 {
    return @atomicLoad(u32, p, .unordered); // SPAN: unordered atomic load
}

fn notExported(x: u32) u32 {
    return x +% 1;
}

export fn callsMissing(x: u32) u32 {
    return notExported(x); // SPAN: call to a function outside the selected AIR
}
