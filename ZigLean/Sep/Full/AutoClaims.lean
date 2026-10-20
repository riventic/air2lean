import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AllocSpec

/-!
# `fsym` rules for byte-range claims (`docs/sep-full-state.md` §Byte-range claims)

A claim `bclaim b lo hi t` is the union of its bytes' claims, so the planner treats claims like
regions without bytes (`docs/proof-automation.md` §Range laws):

* `bclaim_split` is a **range law** (`@[fsym_plan]`): a claim of the postcondition is carved out of
  a claim of the state of the same block and tag that covers it, and adjacent claims of the state
  are joined first when none covers it (bounds by the arithmetic solver);
* **leftover claims** are dropped (`claim_drop`, `pclaim_drop`, `@[fsym_drop]`): a claim owns no bytes, and a
  dropped claim is never minted again, so dropping one only forgets that its bytes are exclusive.

`pclaim p lo hi t` unfolds to `bclaim b lo hi t` with the fact `p.block = some b`. Lending,
returning and revoking tagged claims (`EUpd.lendC`, `EUpd.returnC`, `EUpd.revokeC`) are ghost
updates an invariant proof applies by hand, as for tagged shares.
-/

namespace Zig.Full

open FAssn

/-- **Drop a claim**: it owns no bytes and no knowledge. -/
theorem claim_drop {b : BlockId} {lo hi : Nat} {t : STag} {R : FAssn} : EUpd (bclaim b lo hi t ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h)
    (EUpd.drop fun _ h => ⟨h.1, h.2.1, by rw [h.2.2]; exact fun _ _ => rfl⟩)

/-- **Drop a pointer's claim** (one whose block the state has not opened, e.g. the released
bytes' claim of a shrink, `FAllocInv.relBytes`). -/
theorem pclaim_drop {p : Ptr} {lo hi : Nat} {t : STag} {R : FAssn} : EUpd (pclaim p lo hi t ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h) (EUpd.drop fun _ h => pclaim_ghost h)

attribute [fsym_drop] claim_drop pclaim_drop
attribute [fsym_plan] bclaim_split

/-! The other affine ghost resources carry no bytes either. Forgetting them at a return does
not reclaim a byte or mint a replacement claim; it is the existing `EUpd.drop` law. -/

@[fsym_drop] theorem EUpd.epTok_drop {γ e : Nat} {q : Frac} {R : FAssn} :
    EUpd (epTok γ e q ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h) EUpd.dropEp

@[fsym_drop] theorem EUpd.gauthP_drop {γ e : Nat} {M : GMap} {p : STag} {R : FAssn} :
    EUpd (gauthP γ e M p ⋆ R) R :=
  EUpd.dropL fun _ h => ⟨h.1, h.2.1, by rw [h.2.2]; exact fun _ _ => rfl⟩

@[fsym_drop] theorem EUpd.gfrag_drop {γ e i : Nat} {g : GRegion} {R : FAssn} :
    EUpd (gfrag γ e i g ⋆ R) R :=
  EUpd.dropL fun _ h => ⟨h.1, h.2.1, by rw [h.2.2]; exact fun _ _ => rfl⟩

@[fsym_drop] theorem EUpd.bshare_drop {b : BlockId} {q : Frac} {k : Nat} {t : STag} {R : FAssn} :
    EUpd (bshare b q k t ⋆ R) R :=
  EUpd.dropL fun _ h => ⟨h.2.1, h.2.2.1, by rw [h.2.2.2]; exact fun _ _ => rfl⟩

@[fsym_drop] theorem EUpd.bcrcpt_drop {b : BlockId} {lo hi γ e : Nat} {R : FAssn} :
    EUpd (bcrcpt b lo hi γ e ⋆ R) R :=
  EUpd.dropL fun _ h => ⟨h.1, h.2.1, by rw [h.2.2]; exact fun _ _ => rfl⟩

@[fsym_drop] theorem EUpd.pure_drop {φ : Prop} {R : FAssn} : EUpd (⟪φ⟫ ⋆ R) R :=
  EUpd.of_imp fun _ h => (sep_lift.mp h).2

end Zig.Full
