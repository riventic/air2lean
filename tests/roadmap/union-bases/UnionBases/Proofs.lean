import UnionBases.Gen
import ZigLean.Mem.ConstPtr
import Air2Lean.Check

/-!
# Union-member constant pointer bases: generated clients

`UnionBases.Gen` is the retained translation of `air/0.16.0` (`union_bases.zig`; the 0.15.2 and
0.14.1 exports translate to the same definitions). Global 0 (`union_bases.table : Holder`) is
block 0 of `mem0`, global 1 (`union_bases.mixed : Mixed`) block 1. The paths below restate each
exported constant as the projection chain of its source expression, with the type table's
layout: `Holder` puts `low` at 0, `outer` at 16, `ext` at 36, `wide` at 40, `maybe` at 52,
`res` at 68 and `bare` at 76; `Inner.bare` is at 1. Union payloads (`unionPayload index ts ta pa`):
`Wide` has a `u32` tag and payload alignment 2 (payload at 4), `Low` a 1-byte tag and payload
alignment 8 (payload at 0, tag at 8), `Bare` a 1-byte safety tag and alignment 1 (payload at 1),
`Outer` a `u64` tag (payload at 8). An `extern` union member is no projection. No generated body
is replaced.
-/

open Zig Zig.ConstPtr

namespace UnionBasesClients

/-- Global 0 is block 0, global 1 block 1. -/
def blocks : Nat → Option BlockId := fun g => if g < 2 then some g else none

/-- `&table.wide.cells[2]` (`cells` is member 2 of `Wide`). -/
def wideCellPath : Path := ⟨.global 0, [.field 40, .unionPayload 2 4 4 2, .elem 2 2]⟩
/-- `&table.wide.half` (member 1): the same payload address as `cells`. -/
def wideHalfPath : Path := ⟨.global 0, [.field 40, .unionPayload 1 4 4 2]⟩
/-- `&table.low.pair[1]`: payload first. -/
def lowPairPath : Path := ⟨.global 0, [.field 0, .unionPayload 1 1 1 8, .elem 1 1]⟩
/-- `&table.bare.pair[1]`: a bare union behind its safety tag. -/
def barePairPath : Path := ⟨.global 0, [.field 76, .unionPayload 1 1 1 1, .elem 1 1]⟩
/-- `&table.outer.inner.bare.pair[1]`: a union member nested in a union payload. -/
def outerPairPath : Path :=
  ⟨.global 0, [.field 16, .unionPayload 0 8 8 1, .field 1, .unionPayload 1 1 1 1, .elem 1 1]⟩
/-- `&table.maybe.?.cells[1]`: a union member under an optional payload. -/
def maybeCellPath : Path := ⟨.global 0, [.field 52, .optPayload, .unionPayload 2 4 4 2, .elem 2 1]⟩
/-- `&(table.res catch unreachable).bytes[3]`: an `extern` member of an error-union payload
(`Ext`, size 4, alignment 4). -/
def resBytePath : Path := ⟨.global 0, [.field 68, .errPayload 4 4, .elem 1 3]⟩
/-- `&table.ext.word`, `&table.ext.pair.hi`, `&table.ext.bytes[2]`: `extern` members. -/
def extWordPath : Path := ⟨.global 0, [.field 36]⟩
def extHiPath : Path := ⟨.global 0, [.field 36, .field 2]⟩
def extBytePath : Path := ⟨.global 0, [.field 36, .elem 1 2]⟩
/-- `&mixed.raw[3]` (`raw` is member 1 of `Mixed`, payload at 4). -/
def mixedHighPath : Path := ⟨.global 1, [.unionPayload 1 4 4 2, .elem 1 3]⟩

private def root : Ptr := ⟨some 0, 0⟩

private def run {α : Type} (x : MemM α) (m : Mem) : Option (Except Error α) :=
  (x.run m).run.map (·.map Prod.fst)

/-! ## Identity and offsets: generated constant = resolved path = runtime chain -/

theorem wideCell_resolve : resolve blocks wideCellPath = .ok ⟨some 0, 48⟩ := rfl
theorem lowPair_resolve : resolve blocks lowPairPath = .ok ⟨some 0, 1⟩ := rfl
theorem barePair_resolve : resolve blocks barePairPath = .ok ⟨some 0, 78⟩ := rfl
theorem outerPair_resolve : resolve blocks outerPairPath = .ok ⟨some 0, 27⟩ := rfl
theorem maybeCell_resolve : resolve blocks maybeCellPath = .ok ⟨some 0, 58⟩ := rfl
theorem resByte_resolve : resolve blocks resBytePath = .ok ⟨some 0, 71⟩ := rfl
theorem extWord_resolve : resolve blocks extWordPath = .ok ⟨some 0, 36⟩ := rfl
theorem extHi_resolve : resolve blocks extHiPath = .ok ⟨some 0, 38⟩ := rfl
theorem mixedHigh_resolve : resolve blocks mixedHighPath = .ok ⟨some 1, 7⟩ := rfl

theorem wideCellPtr_run (m : Mem) :
    (UnionBases.wideCellPtr.run m).run = some (.ok (⟨some 0, 48⟩, m)) := rfl
theorem lowPairPtr_run (m : Mem) :
    (UnionBases.lowPairPtr.run m).run = some (.ok (⟨some 0, 1⟩, m)) := rfl
theorem barePairPtr_run (m : Mem) :
    (UnionBases.barePairPtr.run m).run = some (.ok (⟨some 0, 78⟩, m)) := rfl
theorem outerPairPtr_run (m : Mem) :
    (UnionBases.outerPairPtr.run m).run = some (.ok (⟨some 0, 27⟩, m)) := rfl
theorem maybeCellPtr_run (m : Mem) :
    (UnionBases.maybeCellPtr.run m).run = some (.ok (⟨some 0, 58⟩, m)) := rfl
theorem resBytePtr_run (m : Mem) :
    (UnionBases.resBytePtr.run m).run = some (.ok (⟨some 0, 71⟩, m)) := rfl
theorem extWordPtr_run (m : Mem) :
    (UnionBases.extWordPtr.run m).run = some (.ok (⟨some 0, 36⟩, m)) := rfl
theorem extHiPtr_run (m : Mem) :
    (UnionBases.extHiPtr.run m).run = some (.ok (⟨some 0, 38⟩, m)) := rfl
theorem mixedHighPtr_run (m : Mem) :
    (UnionBases.mixedHighPtr.run m).run = some (.ok (⟨some 1, 7⟩, m)) := rfl

/-- The constant slice keeps the union-member base as its pointer, and its length. -/
theorem wideSlice_run (m : Mem) :
    (UnionBases.wideSlice.run m).run = some (.ok (⟨⟨some 0, 46⟩, 2⟩, m)) := rfl

/-- The model's runtime chain from the global's root agrees with the resolved constants. -/
theorem wideCell_runtime : runtime root wideCellPath.projs = ⟨some 0, 48⟩ := rfl
theorem outerPair_runtime : runtime root outerPairPath.projs = ⟨some 0, 27⟩ := rfl
theorem maybeCell_runtime : runtime root maybeCellPath.projs = ⟨some 0, 58⟩ := rfl

/-- The generated runtime projections (`struct_field_ptr` of `Holder`, the tag check,
`struct_field_ptr` of the union, `ptr_elem_ptr`) from the global's address give the generated
constant: the table holds `cells`, so the ReleaseSafe check passes. -/
theorem projectWide_identity :
    run (UnionBases.projectWide root) (UnionBases.mem0 .fresh) =
      run UnionBases.wideCellPtr (UnionBases.mem0 .fresh) := by
  decide +kernel

/-- The same for the bare union's safety tag. -/
theorem projectBare_identity :
    run (UnionBases.projectBare root) (UnionBases.mem0 .fresh) =
      run UnionBases.barePairPtr (UnionBases.mem0 .fresh) := by
  decide +kernel

/-! ## Aliasing -/

/-- Members of an `extern` union are at its address: `pair.hi` and `bytes[2]` are one byte. -/
theorem extHi_alias : UnionBases.extHiPtr = UnionBases.extBytePtr := rfl

theorem extHi_alias_model {p q : Ptr} (hp : resolve blocks extHiPath = .ok p)
    (hq : resolve blocks extBytePath = .ok q) : p = q :=
  (resolve_eq_iff (g := 0) (b := 0) rfl hp hq).2 (by decide)

/-- Members of a tagged union alias: `&table.wide.half` is `cells`'s address. -/
theorem wideMembers_alias :
    resolve blocks wideHalfPath = resolve blocks ⟨.global 0, [.field 40, .unionPayload 2 4 4 2]⟩ :=
  unionMembers_alias (ps := [.field 40]) (qs := [])

/-- The tag-first `Wide` payload (its largest member: 6 bytes) is disjoint from its `u32` tag. -/
theorem wide_payload_tag_disjoint {p q : Ptr}
    (hp : resolve blocks ⟨.global 0, [.field 40] ++ [.unionPayload 2 4 4 2]⟩ = .ok p)
    (hq : resolve blocks ⟨.global 0, [.field 40] ++ [.field (unionTagOffset 4 6 2)]⟩ = .ok q) :
    Disjoint p 6 q 4 :=
  unionPayload_tag_disjoint (Nat.le_refl 6) hp hq

/-- The payload-first `Low` payload (8 bytes) is disjoint from its tag at 8. -/
theorem low_payload_tag_disjoint {p q : Ptr}
    (hp : resolve blocks ⟨.global 0, [.field 0] ++ [.unionPayload 1 1 1 8]⟩ = .ok p)
    (hq : resolve blocks ⟨.global 0, [.field 0] ++ [.field (unionTagOffset 1 8 8)]⟩ = .ok q) :
    Disjoint p 8 q 1 :=
  unionPayload_tag_disjoint (Nat.le_refl 8) hp hq

/-- The tags the model's `Zig.Enc` writes are at these offsets (`Wide` at 0, `Low` at 8). -/
theorem tag_offsets : unionTagOffset 4 6 2 = 0 ∧ unionTagOffset 1 8 8 = 8 := by decide

/-- The model's offsets are the translator's `unionLayout` (which places the tag and payload in
the generated `Zig.Enc`), for every union. -/
theorem unionLayout_offsets (ts ta ps pa : Nat) :
    (Air2Lean.unionLayout ts ta ps pa).1 = unionTagOffset ta ps pa ∧
      (Air2Lean.unionLayout ts ta ps pa).2.1 = unionPayloadOffset ts ta pa := by
  unfold Air2Lean.unionLayout unionTagOffset unionPayloadOffset
  by_cases h : pa ≤ ta <;> simp [h]

/-! ## Reads -/

/-- Reads through the constants give the active members' bytes of the program-start table. -/
theorem wideCell_read :
    run (load (BitVec 16) 2 ⟨some 0, 48⟩) (UnionBases.mem0 .fresh) = some (.ok 102) := by
  decide +kernel
theorem barePair_read :
    run (load (BitVec 8) 1 ⟨some 0, 78⟩) (UnionBases.mem0 .fresh) = some (.ok 41) := by
  decide +kernel
theorem outerPair_read :
    run (load (BitVec 8) 1 ⟨some 0, 27⟩) (UnionBases.mem0 .fresh) = some (.ok 52) := by
  decide +kernel
theorem extHi_read :
    run (load (BitVec 16) 2 ⟨some 0, 38⟩) (UnionBases.mem0 .fresh) = some (.ok 0x4433) := by
  decide +kernel
theorem mixedHigh_read :
    run (load (BitVec 8) 1 ⟨some 1, 7⟩) (UnionBases.mem0 .fresh) = some (.ok 63) := by
  decide +kernel

/-- The generated reads at a run-time index through a union-member constant. -/
theorem readWideCell_mem0 :
    run (UnionBases.readWideCell 1) (UnionBases.mem0 .fresh) = some (.ok 101) := by
  decide +kernel
theorem readExtByte_mem0 :
    run (UnionBases.readExtByte 2) (UnionBases.mem0 .fresh) = some (.ok 0x33) := by
  decide +kernel

/-! ## Backends -/

/-- Union payload steps are not misplaced by the LLVM backend (`lowerPtr` uses
`structFieldOffset`): it agrees with the model on every chain without an alignment-1
`eu_payload` step. -/
theorem outerPair_llvm :
    (outerPairPath.projs.map Proj.llvmDelta).sum = total outerPairPath.projs :=
  llvm_total_eq (by decide)

end UnionBasesClients
