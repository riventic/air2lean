import PageThread
import ZigLean.Sep.Full.WitnessStart

/-!
Creation admission from the translated PageAllocator's actual initial memory. The generic
global-selection rule retains every placement and arbitrary input stream; this module supplies
only the generated layout and encoded null facts. It constructs no memory or resource seed.
-/

namespace AllocTranslated.PageAlloc

open Zig Zig.Full Zig.Full.FAssn Zig.Witness

/-- The exact null hint required by creation, in the actual generated start memory. -/
theorem fallocSpec.creation_input_at (_c : Ptr) (σ : Placement)
    (arbitrary : Array (BitVec 64)) :
    FAdmit.At (PageLinux.mem0 σ arbitrary) (aptsE hint (none : Option Ptr)) := by
  apply FAdmit.At.global_aptsE (σ := σ) (gs := _) (j := 0)
    (bs := Enc.encode (none : Option Ptr)) (a := 8) (K := .global) (v := (none : Option Ptr))
  · rfl
  · rfl
  · exact MemAuth.Keep.of_blocks rfl rfl rfl rfl
  · simp [BlockKind.mappedLo]
  · rfl
  · decide
  · decide
  · decide
  · exact LawfulEnc.size_encode _
  · exact LawfulEnc.decode_encode _

/-- The creation precondition is admissible for every placement and arbitrary input stream. -/
theorem fallocSpec.creation_admission (c : Ptr) (σ : Placement)
    (arbitrary : Array (BitVec 64)) : FAdmit (aptsE hint (none : Option Ptr)) := by
  refine FAdmit.iff_at.mpr ⟨PageLinux.mem0 σ arbitrary, ?_,
    fallocSpec.creation_input_at c σ arbitrary⟩
  refine Mem.FSeq.congrMem (Mem.init_fseq σ _ ?_) rfl rfl ?_
  · decide +kernel
  · exact singleThread_empty rfl (by change 0 < 1; decide)

-- The precondition is independent of the context pointer. The universally quantified theorem
-- above supplies the existing existential witness without narrowing that theorem's domain.
nonvacuity_witness fallocSpec.creation :=
  ⟨(⟨none, 0⟩ : Ptr), fallocSpec.creation_admission ⟨none, 0⟩ .fresh #[]⟩

end AllocTranslated.PageAlloc

namespace AllocTranslated.PageThread

open Zig Zig.Full Zig.Full.FAssn Zig.Witness

/-- Both the context pointer and the caller's target type are visible contract arguments. -/
def cAllocSpec.creationParameters : FAllocCreationParameters := ⟨[0, 1], []⟩

/-- The concurrent contract has the same initialized state, for every caller's target type. -/
theorem cAllocSpec.creation (c : Ptr) {Tgt : Type} :
    FTotalTriple (aptsE PageAlloc.hint (none : Option Ptr)) (pure ())
      (fun _ => PageAlloc.ainv.creationPost) :=
  PageAlloc.fallocSpec.creation c

nonvacuity_witness cAllocSpec.creation :=
  ⟨(⟨none, 0⟩ : Ptr), Unit,
    PageAlloc.fallocSpec.creation_admission ⟨none, 0⟩ .fresh #[]⟩

end AllocTranslated.PageThread
