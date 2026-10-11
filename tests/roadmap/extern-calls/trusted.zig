//! An extern call bound to a trusted-base model (`registry.json`, `Model.lean`) at its linker
//! identity: symbol `abs` of library `c`.

extern "c" fn abs(x: c_int) c_int;

export fn absSum(a: c_int, b: c_int) c_int {
    return abs(a) +% abs(b);
}
