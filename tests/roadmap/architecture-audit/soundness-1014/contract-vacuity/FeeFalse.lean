import ZigLean
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Witness

/-!
# Audit 2026-10-14, finding F2: an allocator contract with an empty fee holds for any code

`FAllocSpec L vt ctx I` (`ZigLean/Sep/Full/AllocSpec.lean`) is a contract that each allocator
implementation proves for an invariant `I` of its own choosing. Nothing asks the implementation
to show that `I` can hold: that `I.own ⋆ I.fee φ` holds in some memory (better: in the memory
right after the allocator's own `init`), or that `I.fits` admits some request. The fee of #302
(`FAllocInv.fee`) is one more place where `I` can be empty: `fee_add` holds for the fee that never
holds, since `False ⋆ False = False`.

`trap` below throws `.illegal` at every entry (natively: illegal behaviour at every call). With
that fee and a token that never holds, it satisfies `FAllocSpec FLogic.total`, the *total*
contract. `AllocNeg.not_fallocSpec` refutes a bad allocator only under the premise that the
fee holds somewhere (`hsat`); that premise is not part of the contract and no allocator proof
(`AllocFba.fallocSpec`, `PageAlloc.fallocSpec`, the arena) states it. The same is true of
`CAllocSpec` (the concurrent form).
-/

open Zig Zig.Full FAssn

namespace Audit1014.FeeFalse

/-- An allocator whose every entry is illegal behaviour. -/
def trap : RawVTable where
  alloc _ _ _ _ := throw .illegal
  resize _ _ _ _ _ := throw .illegal
  remap _ _ _ _ _ := throw .illegal
  free _ _ _ _ := throw .illegal

/-- An invariant whose fee and token never hold; `own` is `emp`. -/
def I : FAllocInv where
  own := emp
  tok _ _ _ _ _ _ _ _ := fun _ => False
  fee _ := fun _ => False
  fee_add _ _ _ _ := by
    funext r
    apply propext
    constructor
    · intro h; exact h.elim
    · rintro ⟨_, _, _, _, h, _⟩; exact h

theorem vac {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} (h : ∀ r, P r → False) :
    FTotalTriple P c Q :=
  ⟨fun _ r _ _ hp _ => (h r hp).elim, fun _ r _ _ hp _ => (h r hp).elim⟩

/-- **The trapping allocator satisfies the total allocator contract.** -/
theorem trap_spec (ctx : Ptr) : FAllocSpec FLogic.total trap ctx I where
  alloc _ _ _ _ _ _ _ := vac fun _ ⟨_, _, _, _, _, h⟩ => h
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    vac fun _ ⟨_, _, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, h, _⟩, _⟩⟩ => h
  remap _ _ _ _ _ _ _ _ _ _ _ :=
    vac fun _ ⟨_, _, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, _, ⟨_, _, _, _, h, _⟩⟩⟩⟩ => h
  free _ _ _ _ _ _ _ _ :=
    vac fun _ ⟨_, _, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, _, ⟨_, _, _, _, h, _⟩⟩⟩⟩ => h

/-- Establishing only `own` is insufficient: this real total theorem and its FAdmit witness
must be rejected as a creation companion because the allocator's fee never holds. -/
def trap_spec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem trap_spec.creation (_ctx : Ptr) :
    FTotalTriple emp (pure ())
      (fun _ => ⟪∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ I.fits len.toNat k⟫ ⋆ I.own) :=
  (FTotalTriple.ret (Q := fun _ : Unit => emp) ()).post fun _ _ hp =>
    Full.sep_lift.mpr ⟨⟨1, 0, by decide, by decide, trivial⟩, hp⟩

nonvacuity_witness trap_spec.creation :=
  ⟨⟨none, 0⟩, Zig.Witness.FAdmit.of_emp⟩

theorem no_creation {P : FAssn} {c : MemM Unit}
    (ht : FTotalTriple P c (fun _ => I.creationPost)) (ha : Zig.Witness.FAdmit P) : False := by
  obtain ⟨_, _, _, _, _, hp, _, _⟩ := Zig.Witness.FAdmit.of_total ht ha
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hp⟩ := Full.sep_lift.mp hp
  obtain ⟨_, _, _, _, _, hfee⟩ := hp
  exact hfee

/-- Every call of `trap` is illegal behaviour. -/
theorem trap_alloc_illegal (ctx : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (m : Mem) :
    ((trap.alloc ctx len k ra).run m).run = some (.error .illegal) := rfl

end Audit1014.FeeFalse

#print axioms Audit1014.FeeFalse.trap_spec
