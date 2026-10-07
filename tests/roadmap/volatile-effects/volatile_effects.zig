//! L13 real-export fixture (docs/volatile-effects.md). Every function but `keepVolatile`
//! performs or launders one volatile (device-facing) access, which the checker must
//! reject with VOLATILE_ACCESS; `keepVolatile` only forms a volatile pointer value.

/// MMIO-style read through a volatile register pointer.
pub fn mmioRead(reg: *volatile u32) u32 {
    return reg.*;
}

/// MMIO-style write.
pub fn mmioWrite(reg: *volatile u32, value: u32) void {
    reg.* = value;
}

/// A fixed device address. The integer pointer constant is rejected independently.
pub fn mmioFixed() u32 {
    const reg: *volatile u32 = @ptrFromInt(0x4000_0000);
    return reg.*;
}

/// A volatile read of a local: never forwarded as a read-only copy.
pub fn localVolatile() u32 {
    var x: u32 = 5;
    const p: *const volatile u32 = &x;
    return p.*;
}

/// An item of a volatile slice.
pub fn sliceRead(s: []volatile u8, i: usize) u8 {
    return s[i];
}

/// `@volatileCast` away: later accesses would look ordinary.
pub fn dropVolatile(p: *volatile u32) *u32 {
    return @volatileCast(p);
}

/// Accepted: a volatile pointer value is address metadata only.
pub fn keepVolatile(p: *u32) *volatile u32 {
    return p;
}

comptime {
    _ = &mmioRead;
    _ = &mmioWrite;
    _ = &mmioFixed;
    _ = &localVolatile;
    _ = &sliceRead;
    _ = &dropVolatile;
    _ = &keepVolatile;
}
