import AllocFba.Creation

/-!
# The remaining empty-backing boundary

These controls distinguish the translated initializer's value behavior from the backing
resources required by the current invariant. No memory or ownership seed is constructed.
-/

namespace AllocFba.FBA.CreationDomain

open Zig Zig.Full Zig.Full.FAssn Gen

/-- Initialization copies any zero-length slice and starts at index zero. This value-level
fact does not assert pointer validity or admission of the invariant's backing resources. -/
theorem init_empty_value (p : Ptr) :
    FTotalTriple emp (heap_FixedBufferAllocator_init ⟨p, 0⟩)
      (fun v => ⟪ v.buffer = (⟨p, 0⟩ : Slice) ∧ v.end_index = 0 ⟫) := by
  fsym

/-- A share of any bound, including zero, requires a nonempty live backing block. In
particular, the current `fparts` share cannot describe a slice backed by a zero-byte block. -/
theorem empty_backing_no_share {m : Mem} {r rF : Res} {b : BlockId} {blk : Block}
    {q : Frac} {k : Nat} {R : FAssn} (hh : Holds m r rF)
    (hb : m.blocks[b]? = some blk) (hempty : blk.bytes.size = 0) :
    ¬ (bshare b q k ⋆ R) r := by
  intro hp
  obtain ⟨actual, ha, -, -, hlive⟩ := hh.bshare hp
  rw [hb] at ha
  cases ha
  omega

end AllocFba.FBA.CreationDomain
