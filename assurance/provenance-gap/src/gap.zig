//! Second provenance fixture (I07): an aarch64-linux, ReleaseSafe example whose source, fresh
//! schema-12 AIR, generated Lean, proofs, proof receipt and native build are chained by
//! assurance/provenance-gap/manifest.json (see assurance/provenance for the x86_64 fixture).

pub fn gap(a: u32, b: u32) u32 {
    return if (a > b) a - b else b - a;
}

pub fn within(a: u32, b: u32, tolerance: u32) bool {
    return gap(a, b) <= tolerance;
}

pub fn main() u8 {
    return if (within(40, 42, 2)) 0 else 1;
}

comptime {
    _ = &gap;
    _ = &within;
}
