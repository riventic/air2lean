import ZigLean.Float

namespace AssuranceFixture

-- A numerical theorem outside the shipped registry: the audit must reject it until a
-- reviewed float-semantics label states which semantics it concerns (docs/float-semantics.md).
theorem float_add_self (x : Zig.F64) : Zig.Float.add x x = Zig.Float.add x x := rfl

-- Not numerical: needs no label.
theorem nat_add_self (n : Nat) : n + n = n + n := rfl

end AssuranceFixture
