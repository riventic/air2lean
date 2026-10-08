//! Provenance fixture (I07): the smallest example whose source, fresh schema-12 AIR, generated
//! Lean, proofs, proof receipt and native build are chained by assurance/provenance/manifest.json.

pub fn add(a: u32, b: u32) u32 {
    return a +% b;
}

pub fn double(x: u32) u32 {
    return add(x, x);
}

pub fn main() u8 {
    return @truncate(double(21));
}

comptime {
    _ = &add;
    _ = &double;
}
