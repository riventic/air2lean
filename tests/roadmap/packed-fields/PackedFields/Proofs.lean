import PackedFields.Gen
import ZigLean.PackedLemmas

/-!
# Packed fields and bit-pointers (L08)

`PackedFields.Gen` is the retained translation of `air/0.16.0` (`README.md` has the Zig source).
`reg` and `word` start wholly undefined. Each client runs a function from `mem0`:

* a field store sets only the field's bits (defined-bit masks): the field reads back although
  the rest of its host is undefined, and the adjacent field in the same byte keeps its value;
* a store of `undefined` makes only the field's bits undefined: the adjacent field in the same
  byte keeps its value, the field itself reads as `.unspecified`;
* a field that crosses a byte boundary (`inner`, bits 4 to 15), a byte pointer under a
  bit-pointer (`inner.c`, byte 1), signed, `bool` and enum fields, a packed union's struct
  field, both host widths (3 bytes on LLVM, the ABI size 4 on x86_64) and a stack block.

The general frame theorems are in `ZigLean/PackedLemmas.lean`.
-/

open PackedFields Zig

namespace PackedFieldsClients

/-- The result of running `f` from `mem0`. -/
def result {α : Type} (f : MemM α) : Option (Except Error α) :=
  ((f.run mem0).run).map (·.map Prod.fst)

/-- `reg.a = 5; return reg.a;`: the other 20 bits of the host are still undefined. -/
theorem setA_ok : result setA = some (.ok 5) := by decide +kernel

/-- `inner.c` is a byte pointer to byte 1 of the host (bit 4 + 4 = 8), not to byte 0. -/
theorem innerC_ok : result innerC = some (.ok 0xAB) := by decide +kernel

/-- The byte store to `inner.c` leaves `a` (bits 0 to 3 of byte 0) as it was. -/
theorem innerCKeepsA_ok : result innerCKeepsA = some (.ok 1) := by decide +kernel

/-- A 12-bit field across bytes 0 and 1 reads back. -/
theorem setInner_ok : result setInner = some (.ok { b := 2, c := 0x5A }) := by decide +kernel

/-- `inner.b` is still undefined: loading all of `inner` is `.unspecified`. -/
theorem innerPartial_undefined : result innerPartial = some (.error .unspecified) := by
  decide +kernel

/-- `reg.inner.b = undefined` (bits 4 to 7) keeps `a` (bits 0 to 3 of the same byte). -/
theorem undefKeepsA_ok : result undefKeepsA = some (.ok 3) := by decide +kernel

/-- After `reg.inner.b = undefined`, `inner.b` is undefined, not 7 and not a default. -/
theorem undefField_undefined : result undefField = some (.error .unspecified) := by
  decide +kernel

/-- `reg.s = -3` in a signed 5-bit field. -/
theorem signedS_ok : result signedS = some (.ok (-3)) := by decide +kernel

theorem boolOn_ok : result boolOn = some (.ok true) := by decide +kernel

theorem modeHigh_ok : result modeHigh = some (.ok .high) := by decide +kernel

/-- `word.raw = 0x123456; word.reg.a = 0xF;` changes only bits 0 to 3. -/
theorem unionRaw_ok : result unionRaw = some (.ok 0x12345F) := by decide +kernel

/-- Mode bits 3 (`0xC00000`) are no `Mode`: `.illegal`. -/
theorem unionBadMode_illegal : result unionBadMode = some (.error .illegal) := by decide +kernel

/-- The x86_64 host width (the ABI size, 4 bytes) gives the same field values. -/
theorem hostAbi_ok : result hostAbi = some (.ok 9) := by decide +kernel

/-- A local with a store of `undefined` to a field is a stack block; `a` keeps its value. -/
theorem localUndef_ok : result localUndef = some (.ok 6) := by decide +kernel

end PackedFieldsClients
