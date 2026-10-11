import UndefOperands.Gen

/-!
# Partly `undefined` constant operands are undefined bytes

`UndefOperands.Gen` is the retained translation of `air/0.16.0`. Each store of a partly
`undefined` struct or array constant writes the defined parts' encoding and leaves the bytes of
each `undefined` item or field undefined, in one store. A later read of a defined part returns
it; a read of an `undefined` part throws `.unspecified` (never a default `0`). Each run is a
kernel computation, so it is stated for one placement of the stack blocks (`∃ σ`): the
outcome does not observe an address.
-/

open UndefOperands Zig

namespace UndefOperandsClients

/-- `var s: Pair = .{ .a = 1, .b = undefined }; return s.a;` (the local is a stack block). -/
theorem localA_defined :
    ∃ σ, ((localA.run (mem0 σ)).run).map (·.map Prod.fst) = some (.ok 1) :=
  ⟨.fresh, by decide +kernel⟩

/-- `return s.b` reads the undefined field: `.unspecified`, not `0`. -/
theorem localB_undefined :
    ∃ σ, ((localB.run (mem0 σ)).run).map (·.map Prod.fst) = some (.error .unspecified) :=
  ⟨.fresh, by decide +kernel⟩

/-- `rec = .{ .len = 2, .buf = .{ 1, undefined, 3 } }; return rec.len;` -/
theorem recLen_defined :
    ∃ σ, ((recLen.run (mem0 σ)).run).map (·.map Prod.fst) = some (.ok 2) :=
  ⟨.fresh, by decide +kernel⟩

/-- `return rec.buf[1]` reads the undefined nested array item: `.unspecified`. -/
theorem recMid_undefined :
    ∃ σ, ((recMid.run (mem0 σ)).run).map (·.map Prod.fst) = some (.error .unspecified) :=
  ⟨.fresh, by decide +kernel⟩

end UndefOperandsClients
