import UndefOperands.Gen

/-!
# Partly `undefined` constant operands are undefined bytes

`UndefOperands.Gen` is the retained translation of `air/0.16.0`. Each store of a partly
`undefined` struct or array constant writes the defined parts' encoding and leaves the bytes of
each `undefined` item or field undefined, in one store. A later read of a defined part returns
it; a read of an `undefined` part throws `.unspecified` (never a default `0`).
-/

open UndefOperands Zig

namespace UndefOperandsClients

/-- `var s: Pair = .{ .a = 1, .b = undefined }; return s.a;` (the local is a stack block). -/
theorem localA_defined : ((localA.run mem0).run).map (·.map Prod.fst) = some (.ok 1) := by
  decide +kernel

/-- `return s.b` reads the undefined field: `.unspecified`, not `0`. -/
theorem localB_undefined :
    ((localB.run mem0).run).map (·.map Prod.fst) = some (.error .unspecified) := by
  decide +kernel

/-- `rec = .{ .len = 2, .buf = .{ 1, undefined, 3 } }; return rec.len;` -/
theorem recLen_defined : ((recLen.run mem0).run).map (·.map Prod.fst) = some (.ok 2) := by
  decide +kernel

/-- `return rec.buf[1]` reads the undefined nested array item: `.unspecified`. -/
theorem recMid_undefined :
    ((recMid.run mem0).run).map (·.map Prod.fst) = some (.error .unspecified) := by
  decide +kernel

end UndefOperandsClients
