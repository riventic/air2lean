import PackedFieldsFresh.Gen
import PackedFieldsX86.Gen
import ZigLean.PackedLemmas

/-!
# Packed fields: the compiler export (L08)

`PackedFieldsFresh.Gen` translates `air-fresh/0.16.0/llvm`, the unmodified export of
`packed_fields.zig` from a patched 0.16.0 compiler on the LLVM backend (`README.md`
§Compiler export). `PackedFieldsX86.Gen` translates `air-fresh/0.16.0/x86_64`, `hostAbi` from
the self-hosted x86_64 backend, whose bit-pointers have the ABI host size 4. These are the same
client results as `PackedFields.Proofs` proves for the hand-written AIR. The compiler folds
`&reg.inner.c` and the like into constant pointers (`global`, offset 0), so the generated
bit-pointer accesses carry the pointer as a literal instead of a `struct_field_ptr` instruction,
and it stores a packed aggregate field by field.
-/

open Zig

namespace PackedFieldsFreshClients

/-- The result of running `f` from `mem0`. -/
def result {α : Type} (m : Zig.Mem) (f : MemM α) : Option (Except Error α) :=
  ((f.run m).run).map (·.map Prod.fst)

open PackedFieldsFresh

theorem setA_ok : result mem0 setA = some (.ok 5) := by decide +kernel

theorem innerC_ok : result mem0 innerC = some (.ok 0xAB) := by decide +kernel

theorem innerCKeepsA_ok : result mem0 innerCKeepsA = some (.ok 1) := by decide +kernel

/-- The compiler stores `inner.b` and `inner.c` separately; the 12-bit read still gives both. -/
theorem setInner_ok : result mem0 setInner = some (.ok { b := 2, c := 0x5A }) := by
  decide +kernel

theorem innerPartial_undefined : result mem0 innerPartial = some (.error .unspecified) := by
  decide +kernel

theorem undefKeepsA_ok : result mem0 undefKeepsA = some (.ok 3) := by decide +kernel

theorem undefField_undefined : result mem0 undefField = some (.error .unspecified) := by
  decide +kernel

theorem signedS_ok : result mem0 signedS = some (.ok (-3)) := by decide +kernel

theorem boolOn_ok : result mem0 boolOn = some (.ok true) := by decide +kernel

theorem modeHigh_ok : result mem0 modeHigh = some (.ok .high) := by decide +kernel

theorem unionRaw_ok : result mem0 unionRaw = some (.ok 0x12345F) := by decide +kernel

theorem unionBadMode_illegal : result mem0 unionBadMode = some (.error .illegal) := by
  decide +kernel

/-- The LLVM export of `hostAbi` (host width 3) gives the same value. -/
theorem hostAbi_llvm_ok : result mem0 hostAbi = some (.ok 9) := by decide +kernel

theorem localUndef_ok : result mem0 localUndef = some (.ok 6) := by decide +kernel

/-- `inner_g` is a plain `Inner` global: its bit-pointers have host size 2. -/
theorem bytePtr_ok : result mem0 bytePtr = some (.ok 0xCD) := by decide +kernel

/-- Through a runtime pointer to `reg` (global 0) the compiler keeps `struct_field_ptr_index_N`
instructions; `&r.inner.c` is a bit-pointer `*align(4:8:3) u8`, not a byte pointer. -/
def regPtr : Zig.Ptr := ⟨some 0, 0⟩

theorem innerCPtr_ok : result mem0 (innerCPtr regPtr) = some (.ok 0xAB) := by decide +kernel

theorem innerCKeepsAPtr_ok : result mem0 (innerCKeepsAPtr regPtr) = some (.ok 1) := by
  decide +kernel

theorem setInnerPtr_ok : result mem0 (setInnerPtr regPtr) = some (.ok { b := 2, c := 0x5A }) := by
  decide +kernel

/-- `hostAbi` from the self-hosted x86_64 backend: bit-pointers of host size 4. -/
theorem hostAbi_x86_ok : result PackedFieldsX86.mem0 PackedFieldsX86.hostAbi = some (.ok 9) := by
  decide +kernel

end PackedFieldsFreshClients
