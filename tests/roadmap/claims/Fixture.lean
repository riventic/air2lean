import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.WitnessStart
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.AutoAll

/-!
Claim-strength fixtures. `scripts/claims.py` classifies each theorem from the statement
structure that `tools/Assurance.lean` extracts from its kernel type. No name or comment here is
read by the classifier. `diverge`, `ret` and `boom` stand in for generated roots.

The registered heads are the full-state ones (`FTriple`, `FTotalTriple`, `CTriple`, `FTTriple`,
`FTTotalTriple`). The last section declares deliberate spoofs of reserved (retired) head names;
library code must never import this module.
-/

open Zig

namespace ClaimAllocator

open Zig.Full Zig.Full.FAssn Zig.Witness

def vt : RawVTable where
  alloc _ _ _ _ := pure none
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

def goodInv : FAllocInv where
  own := emp
  tok _ _ _ _ _ _ _ _ := ⟪False⟫

def falseInv : FAllocInv where
  own := ⟪False⟫
  tok _ _ _ _ _ _ _ _ := emp

def emptyDomainInv : FAllocInv := { goodInv with fits := fun _ _ => False }

def outOfRangeInv : FAllocInv := { goodInv with fits := fun n _ => n = 2 ^ 64 }

/-- An unrepresentable natural number is not an accepted allocator request. -/
theorem outOfRange_noCreation (r : Res) (h : outOfRangeInv.creationPost r) : False := by
  obtain ⟨φ, h⟩ := h
  obtain ⟨⟨_, len, k, _, _, hfit⟩, _⟩ := sep_lift.mp h
  have bound := len.isLt
  change len.toNat = 2 ^ 64 at hfit
  omega

theorem goodSpec (ctx : Ptr) : FAllocSpec FLogic.total vt ctx goodInv where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

def goodSpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem goodSpec.creation (_ctx : Ptr) : FTotalTriple emp (pure ()) (fun _ => goodInv.creationPost) := by
  have usable : ∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ goodInv.fits len.toNat k :=
    ⟨1, 0, by decide, by decide, trivial⟩
  fsym [goodInv.creationPost_intro Frac.one (by decide) usable]

nonvacuity_witness goodSpec.creation := ⟨p0, FAdmit.of_emp⟩

/-- The audit spike's impossible `own` still satisfies a bare contract; the claim gate must
reject its use because no creation triple with an admissible precondition can establish it. -/
theorem falseSpec (ctx : Ptr) : FAllocSpec FLogic.total vt ctx falseInv where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym

/-- A real total creation theorem for another invariant must not authenticate this contract. -/
theorem wrongSpec (ctx : Ptr) : FAllocSpec FLogic.total vt ctx falseInv := falseSpec ctx
def wrongSpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem wrongSpec.creation (ctx : Ptr) : FTotalTriple emp (pure ()) (fun _ => goodInv.creationPost) := goodSpec.creation ctx
nonvacuity_witness wrongSpec.creation := ⟨p0, FAdmit.of_emp⟩

/-- A same-named theorem whose statement is not FAdmit cannot authenticate the precondition. -/
theorem wrongAdmit (ctx : Ptr) : FAllocSpec FLogic.total vt ctx goodInv := goodSpec ctx
def wrongAdmit.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem wrongAdmit.creation (ctx : Ptr) : FTotalTriple emp (pure ()) (fun _ => goodInv.creationPost) := goodSpec.creation ctx
theorem wrongAdmit.creation.nonvacuous : True := trivial

/-- Dropping an unused, impossible contract hypothesis would authenticate a vacuous theorem. -/
theorem impossibleSpec (_h : False) : FAllocSpec FLogic.total vt ⟨none, 0⟩ goodInv := False.elim _h
def impossibleSpec.creationParameters : FAllocCreationParameters := ⟨[], [0]⟩
theorem impossibleSpec.creation : FTotalTriple emp (pure ()) (fun _ => goodInv.creationPost) := goodSpec.creation p0
nonvacuity_witness impossibleSpec.creation := FAdmit.of_emp

/-- A positive fee and state alone do not inhabit an allocator's accepted request domain. -/
theorem emptyDomainSpec (ctx : Ptr) : FAllocSpec FLogic.total vt ctx emptyDomainInv where
  alloc _ _ _ _ _ _ hfit := False.elim hfit
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ hfit _ _ _ := False.elim hfit
  remap _ _ _ _ _ _ _ _ hfit _ _ := False.elim hfit
  free _ _ _ _ _ _ _ _ := by fsym

def emptyDomainSpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem emptyDomainSpec.creation (_ctx : Ptr) :
    FTotalTriple emp (pure ()) (fun _ => emptyDomainInv.own ⋆ emptyDomainInv.fee Frac.one) := by fsym
nonvacuity_witness emptyDomainSpec.creation := ⟨p0, FAdmit.of_emp⟩

/-- Creating only the good member cannot authenticate a family with impossible other members. -/
def familyInv (n : Nat) : FAllocInv := if n = 0 then goodInv else falseInv
theorem familySpec (n : Nat) : FAllocSpec FLogic.total vt p0 (familyInv n) := by
  by_cases hn : n = 0
  · simpa [familyInv, hn] using goodSpec p0
  · simpa [familyInv, hn] using falseSpec p0
def familySpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem familySpec.creation (_n : Nat) :
    FTotalTriple emp (pure ()) (fun _ => goodInv.creationPost) := goodSpec.creation p0
nonvacuity_witness familySpec.creation := ⟨0, FAdmit.of_emp⟩

/-- Captured native contexts cannot be relabelled as fresh ghosts to erase instance binding. -/
theorem forgedRole (ctx : Ptr) : FAllocSpec FLogic.total vt ctx goodInv := goodSpec ctx
def forgedRole.creationParameters : FAllocCreationParameters := ⟨[], [0]⟩
theorem forgedRole.creation :
    FTotalTriple emp (pure ()) (fun _ => goodInv.creationPost) := goodSpec.creation p0
nonvacuity_witness forgedRole.creation := FAdmit.of_emp

/-- Architecture regression: a visible parameter does not make its raw creation precondition
admissible at every value. The ordinary existential witness only proves the member at zero. -/
def admissionFamilyInv (n : Nat) : FAllocInv where
  own := ⟪n = 0⟫
  tok _ _ _ _ _ _ _ _ := ⟪False⟫
theorem admissionFamilySpec (n : Nat) : FAllocSpec FLogic.total vt p0 (admissionFamilyInv n) where
  alloc _ _ _ _ _ _ _ := by fsym
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by fsym
  remap _ _ _ _ _ _ _ _ _ _ _ := by fsym
  free _ _ _ _ _ _ _ _ := by fsym
def admissionFamilySpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem admissionFamilySpec.creation (n : Nat) :
    FTotalTriple ⟪n = 0⟫ (pure ()) (fun _ => (admissionFamilyInv n).creationPost) := by
  have usable : ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ (admissionFamilyInv n).fits len.toNat k :=
    ⟨1, 0, by decide, by decide, trivial⟩
  fsym [(admissionFamilyInv n).creationPost_intro Frac.one (by decide) usable]
nonvacuity_witness admissionFamilySpec.creation :=
  ⟨0, FAdmit.of_mem (m := {}) ⟨rfl, rfl, rfl, rfl⟩ fseq_default⟩

theorem admissionFamily_not_admit_one : ¬ FAdmit ⟪(1 : Nat) = 0⟫ := by
  rintro ⟨_, _, _, _, hp, _, _⟩
  exact Nat.noConfusion hp.1

/-- Moving the restriction from the spatial precondition to a proof binder does not enlarge
the admitted domain. The entire creation telescope must be checked, including this premise. -/
theorem telescopeFamilySpec (n : Nat) : FAllocSpec FLogic.total vt p0 (admissionFamilyInv n) :=
  admissionFamilySpec n
def telescopeFamilySpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩
theorem telescopeFamilySpec.creation (n : Nat) (h : n = 0) :
    FTotalTriple emp (pure ()) (fun _ => (admissionFamilyInv n).creationPost) := by
  have usable : ∃ len : BitVec 64, ∃ k,
      0 < len.toNat ∧ k < 64 ∧ (admissionFamilyInv n).fits len.toNat k :=
    ⟨1, 0, by decide, by decide, trivial⟩
  fsym [(admissionFamilyInv n).creationPost_intro Frac.one (by decide) usable]
nonvacuity_witness telescopeFamilySpec.creation :=
  ⟨0, rfl, FAdmit.of_emp⟩

theorem use_contract (I : FAllocInv) (_h : FAllocSpec FLogic.total vt ⟨none, 0⟩ I) :
    FTotalTriple emp (pure ()) (fun _ => emp) := by fsym

theorem good_client : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract goodInv (goodSpec ⟨none, 0⟩)

theorem false_client : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract falseInv (falseSpec ⟨none, 0⟩)

/-- Inlining a vacuous contract cannot bypass the named companion obligation. -/
theorem inline_client : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract falseInv (by constructor <;> intros <;> fsym)

/-- A proposition alias around a concrete premise must not hide its creation obligation. -/
def ContractAlias (I : FAllocInv) : Prop := FAllocSpec FLogic.total vt p0 I
theorem alias_client (_h : ContractAlias falseInv) : FTotalTriple emp (pure ()) (fun _ => emp) :=
  by fsym
nonvacuity_witness alias_client :=
  ⟨falseSpec p0, FAdmit.of_emp⟩

/-- A witness proof is part of the evidence closure too: hiding an allocator premise inside a
data structure does not remove the contract used to construct its nonvacuity witness. -/
structure ContractBox (I : FAllocInv) where
  contract : ContractAlias I
theorem boxed_client (_h : ContractBox falseInv) : FTotalTriple emp (pure ()) (fun _ => emp) :=
  by fsym
nonvacuity_witness boxed_client :=
  ⟨⟨falseSpec p0⟩, FAdmit.of_emp⟩

theorem emptyDomain_client : FTotalTriple emp (pure ()) (fun _ => emp) :=
  use_contract emptyDomainInv (emptyDomainSpec ⟨none, 0⟩)

nonvacuity_witness good_client := FAdmit.of_emp
nonvacuity_witness false_client := FAdmit.of_emp
nonvacuity_witness inline_client := FAdmit.of_emp
nonvacuity_witness emptyDomain_client := FAdmit.of_emp

end ClaimAllocator

namespace ClaimFixture

def diverge : MemM Unit := fun _ => ExceptT.mk none

def ret (v : Nat) : MemM Nat := pure v

def boom : MemM Unit := throw Error.panic

/-! Exact runs (`Eq` heads). -/

/-- An exact successful run is a guaranteed return with an exact result. -/
theorem ret_run (v : Nat) (m : Mem) : (ret v).run m = pure (v, m) := rfl

/-- One ground input: the domain is a single point, so the claim is scoped. -/
theorem ret_run_ground (m : Mem) : (ret 7).run m = pure (7, m) := rfl

/-- An exact run that ends in a safety error is not a no-panic claim. -/
theorem panic_run (m : Mem) : boom.run m = throw Error.panic := rfl

/-- The same exact successful run, stated through the result option. -/
theorem ret_some (v : Nat) (m : Mem) : ((ret v).run m).run = some (.ok (v, m)) := rfl

theorem panic_some (m : Mem) : (boom.run m).run = some (.error Error.panic) := rfl

/-- `pure` in `Option` is `some`: wrapping a safety error it states a panic, not a return. -/
theorem panic_pure (m : Mem) : (boom.run m).run = pure (Except.error Error.panic) := rfl

theorem ret_pure_ok (v : Nat) (m : Mem) : ((ret v).run m).run = pure (Except.ok (v, m)) := rfl

/-! Full-state heads. A total head (`FTotalTriple = FTriple ∧ FReturns`) has the premise
telescope of the partial triple inside; a concurrent one (`CTriple`) a thread triple's at a
depth, and its liveness is the run read in the thread (`CLive`). -/

open Full Witness

theorem fret_total (P : FAssn) (v : Nat) : FTotalTriple P (ret v) (fun _ => P) :=
  FTotalTriple.ret (Q := fun _ => P) v

nonvacuity_witness fret_total := ⟨fun _ => True, 0, FAdmit.of_mem trivial fseq_default⟩

theorem fret_partial (P : FAssn) (v : Nat) : FTriple P (ret v) (fun _ => P) :=
  (fret_total P v).toPartial

nonvacuity_witness fret_partial := ⟨fun _ => True, 0, FAdmit.of_mem trivial fseq_default⟩

liveness_witness fret_partial :=
  ⟨fun _ => True, 0, FLive.of_mem trivial fseq_default ⟨_, rfl⟩⟩

/-- A premise over the root's parameter constrains the domain: scoped. -/
theorem fpremise_total (P : FAssn) (v : Nat) (_h : 0 < v) : FTotalTriple P (ret v) (fun _ => P) :=
  fret_total P v

nonvacuity_witness fpremise_total :=
  ⟨fun _ => True, 1, Nat.one_pos, FAdmit.of_mem trivial fseq_default⟩

/-- Partial correctness holds vacuously for divergence; without a liveness witness it is
`safety`. -/
theorem fdiverge_partial (P : FAssn) : FTriple P diverge (fun _ _ => False) :=
  fun _ _ _ _ _ _ => trivial

nonvacuity_witness fdiverge_partial := ⟨fun _ => True, FAdmit.of_mem trivial fseq_default⟩

/-- Vacuity guard: with any admissible input, divergence has no total triple. -/
theorem fdiverge_not_total (P : FAssn) (Q : Unit → FAssn) (h : FAdmit P) :
    ¬ FTotalTriple P diverge Q := by
  intro ht
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := h
  obtain ⟨v, m', hr⟩ := ht.2 m r rF hh hp hs
  cases hr

/-- Definitions are not unfolded: a wrapper does not inherit total strength. -/
def FWrapped (P : FAssn) (c : MemM Nat) : Prop := FTotalTriple P c (fun _ => P)

theorem fwrapped_total (P : FAssn) (v : Nat) : FWrapped P (ret v) := fret_total P v

/-- A conjunction is not classified, even when its parts would establish total correctness. -/
theorem fpartial_and_returns (P : FAssn) (v : Nat) :
    FTriple P (ret v) (fun _ => P) ∧ FReturns P (ret v) :=
  ⟨fret_partial P v, (fret_total P v).2⟩

/-- Vacuity guard: an unsatisfiable precondition makes even divergence totally correct. The
premises (`False`) have no non-vacuity witness, so the theorem supports no claim. -/
theorem ffalse_total (Q : Unit → FAssn) : FTotalTriple (fun _ => False) diverge Q :=
  ⟨fun _ _ _ _ h _ => h.elim, fun _ _ _ _ h _ => h.elim⟩

theorem cret_partial (P : FAssn) (v : Nat) : CTriple P (pure v : ConcM Unit Nat) (fun _ => P) :=
  CTriple.ret (Q := fun _ => P) v

nonvacuity_witness cret_partial :=
  ⟨fun _ => True, 0, CAdmit.of (FTTAdmit.of_mem trivial fseq_default rfl)⟩

liveness_witness cret_partial :=
  ⟨fun _ => True, 0, CLive.of_run 1 (FTTLive.of_mem trivial fseq_default rfl ⟨_, rfl⟩)⟩

theorem tret_total (P : FAssn) (v : Nat) : FTTotalTriple P (ret v) (fun _ => P) :=
  FTTotalTriple.ret (Q := fun _ => P) v

nonvacuity_witness tret_total := ⟨fun _ => True, 0, FTTAdmit.of_mem trivial fseq_default rfl⟩

theorem tret_partial (P : FAssn) (v : Nat) : FTTriple P (ret v) (fun _ => P) :=
  (tret_total P v).toPartial

nonvacuity_witness tret_partial := ⟨fun _ => True, 0, FTTAdmit.of_mem trivial fseq_default rfl⟩

liveness_witness tret_partial :=
  ⟨fun _ => True, 0, FTTLive.of_mem trivial fseq_default rfl ⟨_, rfl⟩⟩

end ClaimFixture

/-! Entry-point roots. `ClaimStart` stands in for a generated module with a memory at program
start (`mem0`): a claim about its root needs a reachability companion
(`reachability_witness`), its premises holding in `mem0 σ` (audit soundness-2026-10-14 F3). -/

namespace ClaimStart

open Full Witness

def mem0 (σ : Placement) : Mem := Mem.ofGlobals σ []

def ret (v : Nat) : MemM Nat := pure v

/-- From the globals at program start. -/
theorem start_total (v : Nat) : FTotalTriple (globals []) (ret v) (fun _ => globals []) :=
  FTotalTriple.ret (Q := fun _ => globals []) v

nonvacuity_witness start_total := ⟨0, FAdmit.init .fresh [] (by decide) (by simp)⟩

reachability_witness start_total :=
  ⟨.fresh, 0, _, _, (initRes_holds .fresh [] (by simp)).1, (initRes_holds .fresh [] (by simp)).2,
    Mem.init_fseq .fresh [] (by decide), trivial⟩

/-- The same claim with a non-vacuity witness in some memory only: not shown reachable. -/
theorem start_unreached (v : Nat) : FTotalTriple (globals []) (ret v) (fun _ => globals []) :=
  start_total v

nonvacuity_witness start_unreached := ⟨0, FAdmit.init .fresh [] (by decide) (by simp)⟩

end ClaimStart

/-! Deliberate spoofs of reserved claim-head names (`assurance/claim-heads.json`, `reserved`).
Each is a trivially true definition with a retired head's name, declared here because the
audit no longer imports the retired modules, so nothing clashes with it. `scripts/claims.py`
rejects every theorem concluding in a reserved name, whatever its module or fingerprint. The
tests also register them in a test-only registry, which gives the bound and premise mechanisms
of `claims.py` real extracted shapes. Never import this module from library code. The other
reserved names are tested on the extracted JSON in `test_claims.py` (the retired modules that
define them are in this module's import closure, or their names are those of the legacy layer). -/

namespace Zig.Conc.Total

def EventuallyReturns {α : Type} (_c : MemM α) (_m : Mem) : Prop := True

def ReturnsWithin {α : Type} (_n : Nat) (_c : MemM α) : Prop := True

def EventuallyReturnsUnder {α : Type} (_Fair : Prop) (_c : MemM α) : Prop := True

end Zig.Conc.Total

namespace ClaimFixture

/-- A spoof concluding in a reserved name, about the root and a fixed initial memory. -/
theorem spoof_eventually (v : Nat) : Zig.Conc.Total.EventuallyReturns (ret v) {} := trivial

/-- A closed bound (`2`) and a bound over a variable (`n + 1`). -/
theorem spoof_within (v : Nat) : Zig.Conc.Total.ReturnsWithin 2 (ret v) := trivial

theorem spoof_within_sym (n v : Nat) : Zig.Conc.Total.ReturnsWithin (n + 1) (ret v) := trivial

/-- A premise-dependent return with an unsatisfiable premise. -/
theorem spoof_under (v : Nat) : Zig.Conc.Total.EventuallyReturnsUnder False (ret v) := trivial

end ClaimFixture
