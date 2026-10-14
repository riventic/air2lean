import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Region

/-!
# Negative checks of `FAllocSpec`

`FAllocSpec` is not vacuous: an allocator that grants the same bytes twice does not satisfy it,
for any invariant whose state and two fees (`FAllocInv.fee`) hold in some memory, in any logic
(`Static.not_fallocSpec`); and an allocator whose `free` traps satisfies it only if no `alloc`
succeeds (`trapFree_alloc_none`). These replace the legacy `AllocSpec/Toy` checks
(`docs/alloc-spec.md`, §Retired claims).

Like the state `own`, the fee is what a client must hold to call `alloc`: an invariant whose
`own` or `fee` never holds makes every triple vacuous, so the checks quantify over invariants
whose precondition holds somewhere (for a fee-free allocator, `fee φ = emp`: `own` alone).
-/

namespace SepFull.AllocNeg

open Zig Zig.Full FAssn

/-- A grant of nonempty bytes owns the cell at its start. -/
theorem granted_cell {I : FAllocInv} {p : Ptr} {k : Nat} {φ : Frac} {bs : Array Byte} {r : Res}
    (hg : I.granted p k φ bs r) (hn : 0 < bs.size) :
    ∃ b fc, p.block = some b ∧ r.heap (b, p.off.toNat) = some fc := by
  obtain ⟨A, S, K, q, r₁, r₂, -, rfl, h1, -⟩ := hg
  obtain ⟨b, hb, -⟩ := h1.1.2.2
  obtain ⟨fc, e, -⟩ := region_cell hb (i := 0) hn h1
  rw [Nat.add_zero] at e
  exact ⟨b, fc, hb, by simp [e]⟩

namespace Static

/-- Every `alloc` returns the same buffer `p`. -/
def vtable (p : Ptr) : RawVTable where
  alloc _ _ _ _ := pure (some p)
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

/-- **No double issue**: no invariant whose state and two fees hold in some memory makes the
static allocator satisfy `FAllocSpec`, in any logic: the second `alloc` would grant bytes that the
first grant still owns. -/
theorem not_fallocSpec (L : FLogic) (p ctx : Ptr) (I : FAllocInv) (hfit : I.fits 1 0)
    (hsat : ∃ φ₁ φ₂ m r rF, Holds m r rF ∧ (I.own ⋆ (I.fee φ₁ ⋆ I.fee φ₂)) r ∧ m.FSeq) :
    ¬ FAllocSpec L (vtable p) ctx I := by
  intro hs
  obtain ⟨φ₁, φ₂, m, r, rF, hh, hI, hst⟩ := hsat
  have t₁ := L.toPartial (L.frame (R := I.fee φ₂) (hs.alloc 1 0 0 φ₁ (by decide) (by decide) hfit))
  have t₂ := L.toPartial (hs.alloc 1 0 0 φ₂ (by decide) (by decide) hfit)
  have r1 : ∃ r', Holds m r' rF ∧
      (I.allocPost (1 : BitVec 64).toNat 0 φ₁ (some p) ⋆ I.fee φ₂) r' ∧ m.FSeq :=
    t₁ m r rF hh (sep_assoc' hI) hst
  obtain ⟨_, hh₁, h₁, hst₁⟩ := r1
  obtain ⟨r₁, rG, hd, rfl, hI₁, bs₁, hG₁⟩ := ac_cast h₁ (Q := (I.own ⋆ I.fee φ₂) ⋆
    FAssn.ex fun bs : Array Byte => ⟪bs.size = (1 : BitVec 64).toNat⟫ ⋆ I.granted p 0 φ₁ bs)
    (by simp only [FAllocInv.allocPost]; ac_rfl)
  obtain ⟨hs₁, hg₁⟩ := sep_lift.mp hG₁
  have r2 : ∃ r', Holds m r' ⟨rG.heap ∪ rF.heap, rG.know.union rF.know, rG.gh.add rF.gh⟩ ∧
      I.allocPost (1 : BitVec 64).toNat 0 φ₂ (some p) r' ∧ m.FSeq :=
    t₂ m r₁ _ (Holds.split hd hh₁) hI₁ hst₁
  obtain ⟨_, hh₂, ⟨r₂, rG₂, -, rfl, -, bs₂, hG₂⟩, -⟩ := r2
  obtain ⟨hs₂, hg₂⟩ := sep_lift.mp hG₂
  obtain ⟨b, fc, hpb, e₁⟩ := granted_cell hg₁ (by simp at hs₁; omega)
  obtain ⟨b', fc', hpb', e₂⟩ := granted_cell hg₂ (by simp at hs₂; omega)
  rw [hpb] at hpb'; cases hpb'
  rcases hh₂.disj (b, p.off.toNat) with e | e
  · simp [e₂] at e
  · simp [e₁] at e

end Static

/-- **`free` is not vacuous**: an allocator whose `free` traps satisfies `FAllocSpec` only if no
`alloc` succeeds. -/
theorem trapFree_alloc_none {L : FLogic} {vt : RawVTable} {ctx : Ptr} {I : FAllocInv}
    (hfree : ∀ s k ra m, (vt.free ctx s k ra).run m = throw .illegal)
    (hs : FAllocSpec L vt ctx I) {m m' : Mem} {r rF : Res} {len : BitVec 64} {k : Nat}
    {ra : BitVec 64} {φ : Frac} {p : Ptr} (hh : Holds m r rF) (hI : (I.own ⋆ I.fee φ) r)
    (hst : m.FSeq) (hl : 0 < len.toNat) (hk : k < 64) (hfit : I.fits len.toNat k)
    (hrun : (vt.alloc ctx len k ra).run m = pure (some p, m')) : False := by
  have a := L.toPartial (hs.alloc len k ra φ hl hk hfit) m r rF hh hI hst
  rw [hrun] at a
  obtain ⟨_, hh', ⟨r₁, rG, hd, rfl, hI₁, bs, hG⟩, hst'⟩ := a
  obtain ⟨hsz, hg⟩ := sep_lift.mp hG
  have f := L.toPartial (hs.free ⟨p, len⟩ k ra φ bs hk (by simp [hsz]) (by omega)) m' _ rF hh'
    ⟨r₁, rG, hd, rfl, hI₁, hg⟩ hst'
  rw [hfree] at f
  cases f

end SepFull.AllocNeg

#print axioms SepFull.AllocNeg.Static.not_fallocSpec
#print axioms SepFull.AllocNeg.trapFree_alloc_none
