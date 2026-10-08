import UndefLocals.Gen

/-!
# A store of `undefined` to a local is undefined bytes

`UndefLocals.Gen` is the retained translation of `air/0.16.0`. A local that receives a store of
a wholly `undefined` value is a byte local (`Zig.Bytes T`): a read of an undefined part throws
`.unspecified` (never a default `0`), a read of a defined part returns it, and a copy of the
whole value (`mk`'s return) keeps its undefined parts undefined. A store of `undefined` that the
next access overwrites (`writtenRead`) is dead and keeps the plain `Locals` field.
-/

open UndefLocals Zig

namespace UndefLocalsClients

/-- `var s: Pair = undefined; s.a = 1; return s.a;` -/
theorem fieldA_defined : fieldA.run = some (.ok 1) := by decide +kernel

/-- `return s.b` reads the undefined field: `.unspecified`, not `0`. -/
theorem fieldB_undefined : fieldB.run = some (.error .unspecified) := by decide +kernel

/-- `mk` returns the bytes of `s`: `a = 1`, `b` undefined. -/
theorem mk_bytes : mk.run = some (.ok (Bytes.set (Bytes.undef Pair) 0 (1 : BitVec 32))) := by
  decide +kernel

/-- A copy of a value with an undefined part, then a read of the defined part: its value. -/
theorem copyA_defined : copyA.run = some (.ok 1) := by decide +kernel

/-- A copy, then a read of the undefined part: `.unspecified`. -/
theorem copyB_undefined : copyB.run = some (.error .unspecified) := by decide +kernel

/-- `var x: u32 = undefined; return x +% 1;` reads the undefined local: `.unspecified`. -/
theorem wholeRead_undefined : wholeRead.run = some (.error .unspecified) := by decide +kernel

/-- `var x: u32 = undefined; x = 5; return x +% 1;` -/
theorem writtenRead_value : writtenRead.run = some (.ok 6) := by decide +kernel

/-- `if (c) x = 5; return x +% 1;`: the written local reads its value. -/
theorem condWrite_written : (condWrite true).run = some (.ok 6) := by decide +kernel

/-- Without the write, the read of the undefined local throws `.unspecified`. -/
theorem condWrite_unwritten : (condWrite false).run = some (.error .unspecified) := by
  decide +kernel

/-- `b: { x = undefined; if (c) break :b; x = 5; } return x +% 1;`: the `break` leaves the
block past the write, so the store of `undefined` is not dead: `.unspecified`. -/
theorem branchOut_break : (branchOut true).run = some (.error .unspecified) := by decide +kernel

/-- Without the `break`, the write reaches the read. -/
theorem branchOut_written : (branchOut false).run = some (.ok 6) := by decide +kernel

end UndefLocalsClients
