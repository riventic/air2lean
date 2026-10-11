import ConstBases.Gen
import ZigLean.Mem.ConstPtr

/-!
# Nested constant pointer bases: generated clients

`ConstBases.Gen` is the retained translation of `air/0.16.0` (`const_bases.zig`). Its global 0
(`const_bases.table : Holder`) is block 0 of `mem0`. The paths below restate each exported
constant as the projection chain of its source expression, with the type table's layout:
`Holder.maybe` at 12, `Holder.res` at 20, `Cell.bytes` at 2, byte arrays of stride 1, and the
`Failure![3]u8` payload of size 3 and alignment 1. No generated body is replaced.
-/

open Zig Zig.ConstPtr

namespace ConstBasesClients

/-- Global 0 is block 0; there is no other global. -/
def blocks : Nat → Option BlockId := fun g => if g = 0 then some 0 else none

/-- `&(table.res catch unreachable)[2]` -/
def resElemPath : Path := ⟨.global 0, [.field 20, .errPayload 3 1, .elem 1 2]⟩
/-- `&table.maybe.?.bytes[1]` -/
def maybeElemPath : Path := ⟨.global 0, [.field 12, .optPayload, .field 2, .elem 1 1]⟩
/-- `&@as([*]const u8, @ptrCast(&table.maybe.?))[3]` -/
def maybeBytePath : Path := ⟨.global 0, [.field 12, .optPayload, .elem 1 3]⟩
/-- `@ptrCast(&table.res)` -/
def resPath : Path := ⟨.global 0, [.field 20]⟩
/-- `&table.res`'s error code: the field at `(errUnionOffsets 3 1).1`. -/
def resCodePath : Path := ⟨.global 0, [.field 20, .field (errUnionOffsets 3 1).1]⟩

private def root : Ptr := ⟨some 0, 0⟩

private def run {α : Type} (x : MemM α) (m : Mem) : Option (Except Error α) :=
  (x.run m).run.map (·.map Prod.fst)

/-! ## Identity and offsets: generated constant = resolved path = runtime chain -/

theorem resElem_resolve : resolve blocks resElemPath = .ok ⟨some 0, 24⟩ := rfl
theorem maybeElem_resolve : resolve blocks maybeElemPath = .ok ⟨some 0, 15⟩ := rfl
theorem res_resolve : resolve blocks resPath = .ok ⟨some 0, 20⟩ := rfl

theorem resElemPtr_run (m : Mem) :
    (ConstBases.resElemPtr.run m).run = some (.ok (⟨some 0, 24⟩, m)) := rfl
theorem maybeElemPtr_run (m : Mem) :
    (ConstBases.maybeElemPtr.run m).run = some (.ok (⟨some 0, 15⟩, m)) := rfl
theorem resCodePtr_run (m : Mem) :
    (ConstBases.resCodePtr.run m).run = some (.ok (⟨some 0, 20⟩, m)) := rfl

/-- The constant slice keeps the nested base as its pointer, and its length. -/
theorem maybeSlice_run (m : Mem) :
    (ConstBases.maybeSlice.run m).run = some (.ok (⟨⟨some 0, 15⟩, 2⟩, m)) := rfl

/-- The model's runtime chain from the global's root agrees with the resolved constants. -/
theorem resElem_runtime : runtime root resElemPath.projs = ⟨some 0, 24⟩ := rfl
theorem maybeElem_runtime : runtime root maybeElemPath.projs = ⟨some 0, 15⟩ := rfl

/-- Every offset in `[0, 32]` of the table's block (its 32 bytes) is in bounds of the program-start
memory, under every placement. -/
theorem table_inBounds (σ : Placement) (o : Int) (h0 : 0 ≤ o) (h1 : o ≤ 32) :
    (ConstBases.mem0 σ).inBounds ⟨some 0, o⟩ = true := by
  obtain ⟨A, hb⟩ : ∃ A, (ConstBases.mem0 σ).blocks[0]? =
      some ⟨Enc.encode (({ head := (1 : BitVec 64), maybe := (some ({ tag := (85 : BitVec 16), bytes := (#v[(10 : BitVec 8), (11 : BitVec 8), (12 : BitVec 8), (13 : BitVec 8)] : Vector (BitVec 8) 4) } : ConstBases.Cell)), res := (.ok (#v[(20 : BitVec 8), (21 : BitVec 8), (22 : BitVec 8)] : Vector (BitVec 8) 3) : Except Zig.ErrName (Vector (BitVec 8) 3)), tail := (99 : BitVec 32) } : ConstBases.Holder)), 1, .constGlobal, true, A⟩ :=
    ⟨_, by simp [ConstBases.mem0, Mem.ofGlobals_getElem?]; rfl⟩
  have hs : (Enc.encode (({ head := (1 : BitVec 64), maybe := (some ({ tag := (85 : BitVec 16), bytes := (#v[(10 : BitVec 8), (11 : BitVec 8), (12 : BitVec 8), (13 : BitVec 8)] : Vector (BitVec 8) 4) } : ConstBases.Cell)), res := (.ok (#v[(20 : BitVec 8), (21 : BitVec 8), (22 : BitVec 8)] : Vector (BitVec 8) 3) : Except Zig.ErrName (Vector (BitVec 8) 3)), tail := (99 : BitVec 32) } : ConstBases.Holder))).size = 32 := by decide +kernel
  exact inBounds_of rfl hb h0 (by simp only [hs]; omega)

/-- The generated runtime projections (`struct_field_ptr`, `unwrap_errunion_payload_ptr`,
`ptr_elem_ptr`) from the global's address give the generated constant: each is in bounds of the
table's block (checked pointer formation, MM-3), under every placement. -/
theorem projectRes_identity (σ : Placement) :
    (ConstBases.projectRes root |>.run (ConstBases.mem0 σ)).run =
      (ConstBases.resElemPtr.run (ConstBases.mem0 σ)).run := by
  have o : (errUnionOffsets (Enc.size (Vector (BitVec 8) 3)) (Enc.align (Vector (BitVec 8) 3))).snd = 2 := by
    decide +kernel
  simp [ConstBases.projectRes, ConstBases.resElemPtr, root, ptrProject, Ptr.add, Ptr.elem,
    errPayloadPtr, table_inBounds, zig_unfold, o]

/-- The same for `struct_field_ptr`, `optional_payload_ptr`, `struct_field_ptr`, `ptr_elem_ptr`. -/
theorem projectMaybe_identity (σ : Placement) :
    (ConstBases.projectMaybe root |>.run (ConstBases.mem0 σ)).run =
      (ConstBases.maybeElemPtr.run (ConstBases.mem0 σ)).run := by
  simp [ConstBases.projectMaybe, ConstBases.maybeElemPtr, root, ptrProject, Ptr.add, Ptr.elem,
    table_inBounds, zig_unfold]

/-! ## Aliasing -/

/-- Two different projection chains to the same byte are the same pointer. -/
theorem maybeByte_alias : ConstBases.maybeBytePtr = ConstBases.maybeElemPtr := rfl

theorem maybeByte_alias_model {p q : Ptr} (hp : resolve blocks maybeBytePath = .ok p)
    (hq : resolve blocks maybeElemPath = .ok q) : p = q :=
  (resolve_eq_iff (g := 0) (b := 0) rfl hp hq).2 (by decide)

/-- The array element is disjoint from its error union's code. -/
theorem resElem_code_disjoint : Disjoint ⟨some 0, 24⟩ 1 ⟨some 0, 20⟩ 2 := by
  right; right; decide

/-- The payload (a different subobject from the error code) is disjoint from the code. -/
theorem resPayload_code_disjoint {p q : Ptr}
    (hp : resolve blocks ⟨.global 0, [.field 20] ++ [.errPayload 3 1]⟩ = .ok p)
    (hq : resolve blocks resCodePath = .ok q) : Disjoint p 3 q 2 :=
  payload_code_disjoint hp hq

/-- The `res` payload and the `maybe` payload are sibling-disjoint subobjects. -/
theorem maybe_res_disjoint {p q : Ptr}
    (hp : resolve blocks ⟨.global 0, [] ++ [.field 12]⟩ = .ok p)
    (hq : resolve blocks ⟨.global 0, [] ++ [.field 20]⟩ = .ok q) : Disjoint p 8 q 6 :=
  sibling_disjoint (by decide) hp hq

/-! ## Reads -/

/-- The read through the nested constant pointer gives the payload's element 2. -/
theorem readResElem_mem0 : run ConstBases.readResElem (ConstBases.mem0 .fresh) = some (.ok 22) := by
  decide +kernel

/-- Zig's LLVM backend addresses the payload at the error code (`llvmPayloadOffset 3 1 = 0`):
its constant reads element 0 instead. The translator rejects the shape on `stage2_llvm`. -/
theorem llvm_constant_reads_other :
    run (load (BitVec 8) 1 ⟨some 0, 20 + llvmPayloadOffset 3 1 + 2⟩) (ConstBases.mem0 .fresh) =
      some (.ok 20) := by
  decide +kernel

theorem llvm_offset_differs : llvmPayloadOffset 3 1 ≠ (errUnionOffsets 3 1).2 :=
  (llvmPayloadOffset_ne_iff 3 1).2 (by decide)

/-! ## Unbacked addresses -/

/-- `@ptrFromInt(0x1000)` never resolves, nested or not. -/
theorem fixed_unbacked :
    resolve blocks ⟨.int 0x1000, [.elem 1 2]⟩ = .error (.unbacked 0x1000) := rfl

/-- A global outside the table has no block. -/
theorem unknown_global : resolve blocks ⟨.global 5, []⟩ = .error (.unknownGlobal 5) := rfl

/-- No object is invented: a read through an unbacked address is `.illegal`. -/
theorem unbacked_read : run (load (BitVec 8) 1 ⟨none, 0x1000⟩) (ConstBases.mem0 .fresh) =
    some (.error .illegal) := by
  decide +kernel

end ConstBasesClients
