import ZigLean.Sep.Full.AutoAll

/-! The same program can have a precise or an erased postcondition. Contracts must follow
the audited conclusion, even when the implementation and every sample happen to return ok. -/

open Zig Full FAssn Witness

namespace OutcomeContracts

def good (n : Nat) : MemM (Except ErrName Nat) := pure (.ok n)

theorem precise (n : Nat) :
    FTotalTriple emp (good n) (fun v => ⟪v = .ok n⟫ ⋆ emp) := by
  unfold good
  fsym

nonvacuity_witness precise := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem erased (n : Nat) : FTotalTriple emp (good n) (fun _ => emp) := by
  unfold good
  fsym

nonvacuity_witness erased := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem conditional (n : Nat) : FTriple emp (good n) (fun v => ⟪v = .ok n⟫ ⋆ emp) := by
  unfold good
  fsym

nonvacuity_witness conditional := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩
liveness_witness conditional := ⟨0, FLive.of_mem ⟨rfl, rfl, rfl⟩ fseq_default ⟨_, rfl⟩⟩

def failed : MemM (Except ErrName Nat) := pure (.error "Timeout")

theorem errorOnly : FTotalTriple emp failed (fun v => ⟪v = .error "Timeout"⟫ ⋆ emp) := by
  unfold failed
  fsym

nonvacuity_witness errorOnly := FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default

def wrapped (n : Nat) : MemM (Option (Except ErrName Nat)) := pure (some (.ok n))

theorem optional (n : Nat) :
    FTotalTriple emp (wrapped n) (fun v => ⟪v = some (.ok n)⟫ ⋆ emp) := by
  unfold wrapped
  fsym

nonvacuity_witness optional := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

/-- Arbitrary predicates are not interpreted as an outcome declaration. -/
theorem unknown (n : Nat) (R : Except ErrName Nat → Prop) (h : R (.ok n)) :
    FTotalTriple emp (good n) (fun v => ⟪R v⟫ ⋆ emp) := by
  unfold good
  fsym

nonvacuity_witness unknown := ⟨0, fun _ => True, trivial, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

structure ReturnFamily where
  Value : Type

/-- A type projection may be instantiated with an error union; it is not known non-error. -/
theorem projected (T : ReturnFamily) (v : T.Value) :
    FTotalTriple emp (pure v : MemM T.Value) (fun _ => emp) := by
  fsym

@[irreducible] def hidden (v : Except ErrName Nat) : Prop := v = .ok 0

theorem opaquePost : FTotalTriple emp (good 0) (fun v => ⟪hidden v⟫ ⋆ emp) := by
  unfold good hidden
  fsym

nonvacuity_witness opaquePost := FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default

theorem exact (n : Nat) (m : Mem) : ((good n).run m).run = some (.ok (.ok n, m)) := rfl
theorem exactError (m : Mem) : (failed.run m).run = some (.ok (.error "Timeout", m)) := rfl
theorem stateFunction (n : Nat) : good n = pure (.ok n) := rfl

/-- An arbitrary function's source pair must not be mistaken for StateT's state pair. -/
def readerPair : ReaderT Nat Result (Except ErrName Nat × Nat) :=
  fun n => pure (.error "Timeout", n)
theorem readerFunction : readerPair = (fun n => pure (.error "Timeout", n)) := rfl

/-- These effects have the same function type; the LHS determines the source return value. -/
def readerStatePair : ReaderT Mem Result (Except ErrName Nat × Mem) :=
  fun m => pure (.error "Timeout", m)
theorem stateViaReader : failed = readerStatePair := rfl
theorem readerViaState : readerStatePair = failed := rfl

/-- A plain function does not declare which part, if any, is a final state. -/
def plainPair : Nat → Result (Except ErrName Nat × Nat) := readerPair
theorem plainFunction : plainPair = readerPair := rfl

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
