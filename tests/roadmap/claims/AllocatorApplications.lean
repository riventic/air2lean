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

/-- A constant spatial precondition does not bind a visible proof argument introduced under False. -/
theorem guarded_spec (n : Nat) (_h : n = 0) : FAllocSpec FLogic.total vt p0 (inv n) where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

def guarded_spec.creationParameters : FAllocCreationParameters := ⟨[0, 1], []⟩

theorem guarded_spec.creation (n : Nat) (h : n = 0) :
    FTotalTriple emp (pure ()) (fun _ => (inv n).creationPost) := by
  subst n
  have usable : ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ (inv 0).fits len.toNat k :=
    ⟨1, 0, by decide, by decide, trivial⟩
  fsym [(inv 0).creationPost_intro Frac.one (by decide) usable]

nonvacuity_witness guarded_spec.creation := ⟨0, rfl, FAdmit.of_emp⟩

theorem no_admit_one : ¬ FAdmit ⟪(1 : Nat) = 0⟫ := by
  rintro ⟨_, _, _, _, hp, _, _⟩
  exact Nat.noConfusion hp.1

theorem use_contract (I : FAllocInv) (_h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

theorem keep_pair {P : Prop} (_first : P) (_second : FTotalTriple emp (pure ()) (fun _ => emp)) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

theorem constant_pre_false_arg : FTotalTriple emp (pure ()) (fun _ => emp) :=
  keep_pair
    (fun h : False => use_contract (inv 1) (guarded_spec 1 h.elim))
    (by fsym)

nonvacuity_witness constant_pre_false_arg := FAdmit.of_emp

theorem use_partial_contract (I : FAllocInv) (_h : FAllocSpec FLogic.partial vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

/-- A genuine generic interface rule forwards an unknown instance; its own constructor has
no body to expand and does not introduce an anonymous concrete implementation. -/
theorem generic_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_partial_contract I h.toPartial

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

/-- Retaining a False context is insufficient: it cannot make its local admission root-bound. -/
theorem false_scope_only : FTotalTriple emp (pure ()) (fun _ => emp) :=
  keep_pair
    (fun h : False =>
      let ha : FAdmit ⟪(1 : Nat) = 0⟫ := h.elim
      keep_pair ha (use_contract (inv 1) (spec 1)))
    (by fsym)

nonvacuity_witness false_scope_only := FAdmit.of_emp

/-- A hypothetical held state inside a semantic continuation is not a real initialized start. -/
theorem hypothetical_holds_only : FTotalTriple emp (pure ()) (fun _ => emp) :=
  keep_pair
    (fun (m : Mem) (r rF : Res) (hh : Holds m r rF)
        (hp : (⟪(1 : Nat) = 0⟫ : FAssn) r) (hs : m.FSeq) =>
      let ha : FAdmit ⟪(1 : Nat) = 0⟫ := ⟨m, r, rF, hh, hp, hs, trivial⟩
      keep_pair ha (use_contract (inv 1) (spec 1)))
    (by fsym)

nonvacuity_witness hypothetical_holds_only := FAdmit.of_emp

/-- Root Holds premises also cannot stand for the explicit exact FAdmit client domain. -/
theorem root_holds_only (m : Mem) (r rF : Res) (hh : Holds m r rF)
    (hp : (⟪(1 : Nat) = 0⟫ : FAssn) r) (hs : m.FSeq) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  let ha : FAdmit ⟪(1 : Nat) = 0⟫ := ⟨m, r, rF, hh, hp, hs, trivial⟩
  keep_pair ha (use_contract (inv 1) (spec 1))

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

/-- Calling a visible value "fresh" cannot bind an existential creator to that actual value. -/
theorem fresh_spec (n : Nat) : FAllocSpec FLogic.total vt p0 (inv n) := spec n

def fresh_spec.creationParameters : FAllocCreationParameters := ⟨[], [0]⟩

theorem fresh_spec.creation : FTotalTriple ⟪(0 : Nat) = 0⟫ (pure ())
    (fun _ => FAssn.ex fun n : Nat => (inv n).creationPost) := by
  have choose_zero : EUpd (inv 0).creationPost (FAssn.ex fun n : Nat => (inv n).creationPost) :=
    EUpd.of_imp fun _ h => ⟨0, h⟩
  fsym [spec.creation 0, choose_zero]

nonvacuity_witness fresh_spec.creation := admit_zero

theorem fresh_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract (inv 1) (fresh_spec 1)

nonvacuity_witness fresh_impossible := FAdmit.of_emp

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

def good_inv : FAllocInv where
  own := emp
  tok _ _ _ _ _ _ _ _ := ⟪False⟫

theorem named_good : FAllocSpec FLogic.total vt p0 good_inv where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

def named_good.creationParameters : FAllocCreationParameters := ⟨[], []⟩

theorem named_good.creation : FTotalTriple emp (pure ()) (fun _ => good_inv.creationPost) := by
  have usable : ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ good_inv.fits len.toNat k :=
    ⟨1, 0, by decide, by decide, trivial⟩
  fsym [good_inv.creationPost_intro Frac.one (by decide) usable]

nonvacuity_witness named_good.creation := FAdmit.of_emp

/-- Valid own creation does not authenticate an unrelated anonymous constructor in the body. -/
theorem named_hidden : FAllocSpec FLogic.total vt p0 good_inv :=
  let I := impossible_inv
  (fun (_ : FAllocSpec FLogic.total vt p0 I) => named_good) (generic_constructor I rfl)

def named_hidden.creationParameters : FAllocCreationParameters := ⟨[], []⟩
theorem named_hidden.creation : FTotalTriple emp (pure ()) (fun _ => good_inv.creationPost) :=
  named_good.creation
nonvacuity_witness named_hidden.creation := FAdmit.of_emp

theorem named_hidden_client : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract good_inv named_hidden

nonvacuity_witness named_hidden_client := FAdmit.of_emp

theorem named_hidden_generic (I : FAllocInv) (h : I.own = ⟪False⟫) :
    FAllocSpec FLogic.total vt p0 good_inv :=
  (fun (_ : FAllocSpec FLogic.total vt p0 I) => named_good) (generic_constructor I h)

def named_hidden_generic.creationParameters : FAllocCreationParameters := ⟨[0, 1], []⟩
theorem named_hidden_generic.creation (I : FAllocInv) (_h : I.own = ⟪False⟫) :
    FTotalTriple emp (pure ()) (fun _ => good_inv.creationPost) := named_good.creation
nonvacuity_witness named_hidden_generic.creation := ⟨impossible_inv, rfl, FAdmit.of_emp⟩

theorem named_hidden_generic_client : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract good_inv (named_hidden_generic impossible_inv rfl)

nonvacuity_witness named_hidden_generic_client := FAdmit.of_emp

theorem named_premise (_foreign : FAllocSpec FLogic.total vt p0 impossible_inv) :
    FAllocSpec FLogic.total vt p0 good_inv := named_good

def named_premise.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem named_premise.creation (_foreign : FAllocSpec FLogic.total vt p0 impossible_inv) :
    FTotalTriple emp (pure ()) (fun _ => good_inv.creationPost) := named_good.creation
nonvacuity_witness named_premise.creation :=
  ⟨generic_constructor impossible_inv rfl, FAdmit.of_emp⟩

theorem generic_wrapper (I : FAllocInv) (h : I.own = ⟪False⟫) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract I (generic_constructor I h)

theorem wrapped_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  generic_wrapper impossible_inv rfl

nonvacuity_witness wrapped_impossible := FAdmit.of_emp

theorem let_alias_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  let producer := generic_constructor
  use_contract impossible_inv (producer impossible_inv rfl)

nonvacuity_witness let_alias_impossible := FAdmit.of_emp

theorem invariant_alias_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  let I := impossible_inv
  use_contract I (generic_constructor I rfl)

nonvacuity_witness invariant_alias_impossible := FAdmit.of_emp

def proofIndex {I : FAllocInv} (_proof : FAllocSpec FLogic.total vt p0 I) : Prop := True

/-- A kernel application in a binder type remains in the audit even if the body ignores it. -/
theorem type_only_impossible
    (_x : (let I := impossible_inv; proofIndex (generic_constructor I rfl))) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

nonvacuity_witness type_only_impossible := ⟨trivial, FAdmit.of_emp⟩

theorem true_post : FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) := by fsym

/-- The proof body can omit a producer that occurs only in a definitionally equal conclusion. -/
theorem conclusion_only_impossible : FTotalTriple emp (pure ())
    (fun _ => ⟪proofIndex (generic_constructor impossible_inv rfl)⟫) := true_post

nonvacuity_witness conclusion_only_impossible := FAdmit.of_emp

theorem beta_ignored_impossible : FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) :=
  let I := impossible_inv
  (fun (_ : FAllocSpec FLogic.total vt p0 I) => true_post) (generic_constructor I rfl)

nonvacuity_witness beta_ignored_impossible := FAdmit.of_emp

theorem indexed_helper (I : FAllocInv) (h : I.own = ⟪False⟫)
    (_x : proofIndex (generic_constructor I h)) :
    FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) := true_post

theorem indexed_apply_impossible : FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) :=
  indexed_helper impossible_inv rfl trivial

nonvacuity_witness indexed_apply_impossible := FAdmit.of_emp

/-- The producer can occur in a specialized callee result omitted by the caller's type. -/
theorem indexed_result (I : FAllocInv) (h : I.own = ⟪False⟫) :
    FTotalTriple emp (pure ()) (fun _ => ⟪proofIndex (generic_constructor I h)⟫) := true_post

theorem indexed_result_impossible : FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) :=
  indexed_result impossible_inv rfl

nonvacuity_witness indexed_result_impossible := FAdmit.of_emp

def prefixed_type (I : FAllocInv) (h : I.own = ⟪False⟫) : Prop :=
  let _ignored : FAllocSpec FLogic.total vt p0 I := generic_constructor I h
  True → FTotalTriple emp (pure ()) (fun _ => ⟪True⟫)

theorem prefixed_helper (I : FAllocInv) (h : I.own = ⟪False⟫) : prefixed_type I h :=
  fun (_ : True) => true_post

theorem prefixed_apply_impossible : FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) :=
  prefixed_helper impossible_inv rfl trivial

nonvacuity_witness prefixed_apply_impossible := FAdmit.of_emp

theorem use_producer
    (make : ∀ I : FAllocInv, I.own = ⟪False⟫ → FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract impossible_inv (make impossible_inv rfl)

theorem higher_order_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_producer generic_constructor

nonvacuity_witness higher_order_impossible := FAdmit.of_emp

/-- A polymorphic helper's checked definition need not mention allocator contracts at all. -/
universe u v

def forward {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) (a : α) : β a := f a

theorem polymorphic_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract impossible_inv ((forward generic_constructor impossible_inv) rfl)

nonvacuity_witness polymorphic_impossible := FAdmit.of_emp

structure ProducerHolder where
  make : ∀ I : FAllocInv, I.own = ⟪False⟫ → FAllocSpec FLogic.total vt p0 I

theorem field_impossible : FTotalTriple emp (pure ()) (fun _ => emp) :=
  let holder : ProducerHolder := ⟨generic_constructor⟩
  use_contract impossible_inv (holder.make impossible_inv rfl)

nonvacuity_witness field_impossible := FAdmit.of_emp

theorem let_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  let forwarder := fun (J : FAllocInv) (proof : FAllocSpec FLogic.total vt p0 J) => proof
  use_contract I (forwarder I h)

theorem invariant_alias_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  let J := I
  use_contract J h

theorem type_only_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I)
    (_x : proofIndex h) : FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

theorem conclusion_only_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => ⟪proofIndex h⟫) := true_post

theorem beta_ignored_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => ⟪True⟫) :=
  (fun (_ : FAllocSpec FLogic.total vt p0 I) => true_post) h

theorem polymorphic_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract I (forward (fun _ : Unit => h) ())

structure InterfaceHolder (I : FAllocInv) where
  spec : FAllocSpec FLogic.total vt p0 I

theorem field_interface (I : FAllocInv) (h : FAllocSpec FLogic.total vt p0 I) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  let holder : InterfaceHolder I := ⟨h⟩
  use_contract I holder.spec

/-- An unknown callback cannot silently discard a known contract producer at this boundary. -/
theorem unknown_forwarder
    (consume : (∀ I : FAllocInv, I.own = ⟪False⟫ → FAllocSpec FLogic.total vt p0 I) →
      FTotalTriple emp (pure ()) (fun _ => emp)) :
    FTotalTriple emp (pure ()) (fun _ => emp) := consume generic_constructor

end AllocatorApplications
