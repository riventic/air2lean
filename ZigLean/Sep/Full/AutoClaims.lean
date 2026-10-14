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
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h) (EUpd.drop fun _ h => ⟨h.1, h.2.1⟩)

/-- **Drop a pointer's claim** (one whose block the state has not opened, e.g. the released
bytes' claim of a shrink, `FAllocInv.relBytes`). -/
theorem pclaim_drop {p : Ptr} {lo hi : Nat} {t : STag} {R : FAssn} : EUpd (pclaim p lo hi t ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h) (EUpd.drop fun _ h => pclaim_ghost h)

attribute [fsym_drop] claim_drop pclaim_drop
attribute [fsym_plan] bclaim_split

end Zig.Full
