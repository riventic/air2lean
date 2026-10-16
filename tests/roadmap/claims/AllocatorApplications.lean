import ZigLean.Sep.Full.WitnessStart
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.AutoAll

/-!
Actual-application controls for allocator creation admission. These are audit fixtures, using
only existing full-state judgments. A generic client carries the exact creation precondition's
`FAdmit` hypothesis; an existential witness at another argument cannot supply it.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Witness

namespace AllocatorApplications

def vt : RawVTable where
  alloc _ _ _ _ := pure none
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

def inv (n : Nat) : FAllocInv where
  own := ⟪n = 0⟫
  tok _ _ _ _ _ _ _ _ := ⟪False⟫

theorem spec (n : Nat) : FAllocSpec FLogic.total vt p0 (inv n) where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

def spec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩

theorem spec.creation (n : Nat) :
    FTotalTriple ⟪n = 0⟫ (pure ()) (fun _ => (inv n).creationPost) := by
  have usable : ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ (inv n).fits len.toNat k :=
    ⟨1, 0, by decide, by decide, trivial⟩
  fsym [(inv n).creationPost_intro Frac.one (by decide) usable]

theorem admit_zero : FAdmit ⟪(0 : Nat) = 0⟫ :=
  FAdmit.of_mem (m := {}) ⟨rfl, rfl, rfl, rfl⟩ fseq_default

nonvacuity_witness spec.creation := ⟨0, admit_zero⟩

theorem no_admit_one : ¬ FAdmit ⟪(1 : Nat) = 0⟫ := by
  rintro ⟨_, _, _, _, hp, _, _⟩
  exact Nat.noConfusion hp.1

theorem use_contract (I : FAllocInv) (_h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

theorem keep_pair {P : Prop} (_first : P) (_second : FTotalTriple emp (pure ()) (fun _ => emp)) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

theorem exact_parameter (n : Nat) (_ha : FAdmit ⟪n = 0⟫) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract (inv n) (spec n)

nonvacuity_witness exact_parameter := ⟨0, admit_zero, FAdmit.of_emp⟩

theorem wrong_parameter (_ha : FAdmit ⟪(0 : Nat) = 0⟫) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract (inv 1) (spec 1)

nonvacuity_witness wrong_parameter := ⟨admit_zero, FAdmit.of_emp⟩

theorem pure_guard_only (n : Nat) (_h : n = 0) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract (inv n) (spec n)

nonvacuity_witness pure_guard_only := ⟨0, rfl, FAdmit.of_emp⟩

theorem checked_let : FTotalTriple emp (pure ()) (fun _ => emp) :=
  let ha : FAdmit ⟪(0 : Nat) = 0⟫ := admit_zero
  keep_pair ha (use_contract (inv 0) (spec 0))

nonvacuity_witness checked_let := FAdmit.of_emp

theorem wrong_let : FTotalTriple emp (pure ()) (fun _ => emp) :=
  let ha : FAdmit ⟪(0 : Nat) = 0⟫ := admit_zero
  keep_pair ha (use_contract (inv 1) (spec 1))

nonvacuity_witness wrong_let := FAdmit.of_emp

/-- The first scoped use must not memoize the later use without its local admission proof. -/
theorem let_scope_does_not_escape : FTotalTriple emp (pure ()) (fun _ => emp) :=
  let first : FTotalTriple emp (pure ()) (fun _ => emp) :=
    let ha : FAdmit ⟪(0 : Nat) = 0⟫ := admit_zero
    keep_pair ha (use_contract (inv 0) (spec 0))
  keep_pair first (use_contract (inv 0) (spec 0))

nonvacuity_witness let_scope_does_not_escape := FAdmit.of_emp

/-- Even a kernel proof of admission under False cannot authenticate an unrestricted use. -/
theorem false_scope_does_not_escape : FTotalTriple emp (pure ()) (fun _ => emp) :=
  keep_pair
    (fun h : False =>
      let ha : FAdmit ⟪(1 : Nat) = 0⟫ := h.elim
      keep_pair ha (use_contract (inv 1) (spec 1)))
    (use_contract (inv 1) (spec 1))

nonvacuity_witness false_scope_does_not_escape := FAdmit.of_emp

/-- The argument after `n` has a dependent type, retained in the application and admission. -/
theorem dependent_spec (n : Nat) (_i : Fin (n + 1)) :
    FAllocSpec FLogic.total vt p0 (inv n) where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

def dependent_spec.creationParameters : FAllocCreationParameters := ⟨[0, 1], []⟩

theorem dependent_spec.creation (n : Nat) (_i : Fin (n + 1)) :
    FTotalTriple ⟪n = 0⟫ (pure ()) (fun _ => (inv n).creationPost) := spec.creation n

nonvacuity_witness dependent_spec.creation := ⟨0, 0, admit_zero⟩

theorem exact_dependent (n : Nat) (i : Fin (n + 1)) (_ha : FAdmit ⟪n = 0⟫) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract (inv n) (dependent_spec n i)

nonvacuity_witness exact_dependent := ⟨0, 0, admit_zero, FAdmit.of_emp⟩

def impossible_inv : FAllocInv where
  own := ⟪False⟫
  tok _ _ _ _ _ _ _ _ := ⟪False⟫

/-- A generic constructor is harmless before specialization. Its actual application still
needs a named implementation with creation evidence when a wrapper fixes the invariant. -/
theorem generic_constructor (I : FAllocInv) (h : I.own = ⟪False⟫) :
    FAllocSpec FLogic.total vt p0 I where
  alloc _ _ _ _ _ _ _ := by simp only [h]; fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by simp only [h]; fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by simp only [h]; fsym
  free _ _ _ _ _ _ _ _ := by simp only [h]; fsym

theorem generic_wrapper (I : FAllocInv) (h : I.own = ⟪False⟫) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract I (generic_constructor I h)

theorem wrapped_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  generic_wrapper impossible_inv rfl

nonvacuity_witness wrapped_impossible := FAdmit.of_emp

end AllocatorApplications
