import ZigLean.Sep.Full.Witness

/-! The same program can have a precise or an erased postcondition. Contracts must follow
the audited conclusion, even when the implementation and every sample happen to return ok. -/

open Zig Full FAssn Witness

namespace OutcomeContracts

def good (n : Nat) : MemM (Except ErrName Nat) := pure (.ok n)

theorem precise (n : Nat) :
    FTotalTriple emp (good n) (fun v => ⟪v = .ok n⟫ ⋆ emp) :=
  (FTotalTriple.ret (Q := fun v : Except ErrName Nat => ⟪v = .ok n⟫ ⋆ emp) (.ok n)).pre
    fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

nonvacuity_witness precise := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem erased (n : Nat) : FTotalTriple emp (good n) (fun _ => emp) :=
  FTotalTriple.ret (Q := fun _ => emp) (.ok n)

nonvacuity_witness erased := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem conditional (n : Nat) : FTriple emp (good n) (fun v => ⟪v = .ok n⟫ ⋆ emp) :=
  (precise n).toPartial

nonvacuity_witness conditional := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩
liveness_witness conditional := ⟨0, FLive.of_mem ⟨rfl, rfl, rfl⟩ fseq_default ⟨_, rfl⟩⟩

def failed : MemM (Except ErrName Nat) := pure (.error "Timeout")

theorem errorOnly : FTotalTriple emp failed (fun v => ⟪v = .error "Timeout"⟫ ⋆ emp) :=
  (FTotalTriple.ret (Q := fun v : Except ErrName Nat => ⟪v = .error "Timeout"⟫ ⋆ emp)
    (.error "Timeout")).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

nonvacuity_witness errorOnly := FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default

def wrapped (n : Nat) : MemM (Option (Except ErrName Nat)) := pure (some (.ok n))

theorem optional (n : Nat) :
    FTotalTriple emp (wrapped n) (fun v => ⟪v = some (.ok n)⟫ ⋆ emp) :=
  (FTotalTriple.ret (Q := fun v : Option (Except ErrName Nat) => ⟪v = some (.ok n)⟫ ⋆ emp)
    (some (.ok n))).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

nonvacuity_witness optional := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

/-- Arbitrary predicates are not interpreted as an outcome declaration. -/
theorem unknown (n : Nat) (R : Except ErrName Nat → Prop) (h : R (.ok n)) :
    FTotalTriple emp (good n) (fun v => ⟪R v⟫ ⋆ emp) :=
  (FTotalTriple.ret (Q := fun v : Except ErrName Nat => ⟪R v⟫ ⋆ emp) (.ok n)).pre
    fun _ hp => sep_lift.mpr ⟨h, hp⟩

nonvacuity_witness unknown := ⟨0, fun _ => True, trivial, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

@[irreducible] def hidden (v : Except ErrName Nat) : Prop := v = .ok 0

theorem opaquePost : FTotalTriple emp (good 0) (fun v => ⟪hidden v⟫ ⋆ emp) :=
  (FTotalTriple.ret (Q := fun v : Except ErrName Nat => ⟪hidden v⟫ ⋆ emp) (.ok 0)).pre
    fun _ hp => sep_lift.mpr ⟨by unfold hidden; rfl, hp⟩

nonvacuity_witness opaquePost := FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default

theorem exact (n : Nat) (m : Mem) : ((good n).run m).run = some (.ok (.ok n, m)) := rfl
theorem exactError (m : Mem) : (failed.run m).run = some (.ok (.error "Timeout", m)) := rfl

/-- Exact failed runs retain the taxonomy's distinct model constructors. -/
def failure (e : Error) : MemM Nat := throw e
theorem panic (m : Mem) : ((failure .panic).run m).run = some (.error .panic) := rfl
theorem illegal (m : Mem) : ((failure .illegal).run m).run = some (.error .illegal) := rfl
theorem unspecified (m : Mem) : ((failure .unspecified).run m).run = some (.error .unspecified) := rfl
theorem timer (m : Mem) : ((failure .unsupportedTimer).run m).run = some (.error .unsupportedTimer) := rfl
theorem deadlock (m : Mem) : ((failure .deadlock).run m).run = some (.error .deadlock) := rfl
theorem trap (m : Mem) : ((failure .trap).run m).run = some (.error .trap) := rfl
theorem stack (m : Mem) : ((failure .stackOverflow).run m).run = some (.error .stackOverflow) := rfl

end OutcomeContracts
