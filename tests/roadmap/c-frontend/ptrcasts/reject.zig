//! G2 negatives that air2lean must reject (`check.sh` reads the diagnostics): error storage
//! cannot enter or leave a `*anyopaque` view, and a cyclic error-bearing graph keeps the strict
//! finite error-storage rules (L10).

const E = error{ Bad, Worse };
const ErrNode = extern struct { next: ?*ErrNode, code: u16 };
const Tagged = struct { next: ?*Tagged, status: E!u32 };

fn launder(p: *anyopaque) *u32 {
    return @ptrCast(@alignCast(p));
}

/// An error union's bytes reached through `*anyopaque`.
pub export fn errorThroughOpaque(a: u32) u32 {
    var eu: E!u32 = if (a == 0) error.Bad else a;
    _ = &eu;
    return launder(@ptrCast(&eu)).*;
}

/// A self-referential struct with an error union, viewed as numeric bytes.
pub export fn cyclicErrorView(a: u32) u32 {
    var t = Tagged{ .next = null, .status = a };
    t.next = &t;
    const raw: *const ErrNode = @ptrCast(@alignCast(&t));
    return raw.code;
}
