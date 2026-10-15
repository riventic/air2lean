import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Witness

/-!
The existential nonvacuity companion for a creation family can choose one visible instance.
This audit control uses only the existing full-state FTotalTriple/FAdmit judgments and fsym.
The native context captures `n`, so it cannot be silently treated as a fresh ghost parameter.
The program proofs are symbolic walks; the logical negations expose the missing domain binding.
-/

namespace AllocatorCreationFamily

open Zig Zig.Full Zig.Full.FAssn Zig.Witness

def vt : RawVTable where
  alloc _ _ _ _ := pure none
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

def inv (n : Nat) : FAllocInv where
  own := ⟪n = 0⟫
  tok _ _ _ _ _ _ _ _ := ⟪False⟫

def pre (n : Nat) : FAssn := ⟪n = 0⟫

/-- The post includes state, a positive available fee, and an accepted real request. -/
def post (n : Nat) : FAssn :=
  ⟪0 < Frac.one.val ∧ ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ (inv n).fits len.toNat k⟫ ⋆
    ((inv n).own ⋆ (inv n).fee Frac.one)

theorem spec (n : Nat) : FAllocSpec FLogic.total vt ⟨none, n⟩ (inv n) where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

private theorem usable_request (n : Nat) :
    0 < Frac.one.val ∧ ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ (inv n).fits len.toNat k :=
  ⟨by decide, 1, 0, by decide, by decide, trivial⟩

theorem creation (n : Nat) : FTotalTriple (pre n) (pure ()) (fun _ => post n) := by
  have usable := usable_request n
  unfold pre post
  fsym

nonvacuity_witness creation :=
  ⟨0, FAdmit.of_mem (m := {}) ⟨rfl, rfl, rfl, rfl⟩ fseq_default⟩

theorem not_admit_pre_one : ¬ FAdmit (pre 1) := by
  rintro ⟨_, _, _, _, hp, _, _⟩
  exact Nat.noConfusion hp.1

theorem not_admit_post_one : ¬ FAdmit (post 1) := by
  rintro ⟨_, _, _, _, hp, _, _⟩
  obtain ⟨_, hp⟩ := sep_lift.mp hp
  exact Nat.noConfusion (sep_lift.mp hp).1

/-- Moving the restriction into a proof binder preserves the same limited domain. -/
theorem creation_guarded (n : Nat) (h : n = 0) :
    FTotalTriple emp (pure ()) (fun _ => post n) := by
  have usable := usable_request n
  unfold post
  fsym

nonvacuity_witness creation_guarded :=
  ⟨0, rfl, FAdmit.of_mem (m := {}) ⟨rfl, rfl, rfl⟩ fseq_default⟩

end AllocatorCreationFamily

#print axioms AllocatorCreationFamily.spec
#print axioms AllocatorCreationFamily.creation
#print axioms AllocatorCreationFamily.creation.nonvacuous
#print axioms AllocatorCreationFamily.not_admit_pre_one
#print axioms AllocatorCreationFamily.not_admit_post_one
#print axioms AllocatorCreationFamily.creation_guarded
#print axioms AllocatorCreationFamily.creation_guarded.nonvacuous
