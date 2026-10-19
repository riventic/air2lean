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

/-- Preserving runners use the source's declared effect, even with a compatible alias. -/
theorem readerRunOnState (m : Mem) :
    ReaderT.run failed m = some (.ok (.error "Timeout", m)) := rfl
theorem stateRunOnReader (m : Mem) :
    StateT.run readerStatePair m = some (.ok (.error "Timeout", m)) := rfl

theorem stateRunPrimeOnState (m : Mem) :
    StateT.run' failed m = some (.ok (.error "Timeout")) := rfl

/-- This projection discards genuine ReaderT source data and must not bind the whole root. -/
theorem stateRunPrimeOnReader (m : Mem) :
    StateT.run' readerStatePair m = some (.ok (.error "Timeout")) := rfl

/-- Identity runners preserve the declared spine even when their type arguments rename it. -/
theorem exceptRunOnState :
    @ExceptT.run Error (ReaderT Mem Option) (Except ErrName Nat × Mem) failed =
      (fun m => some (.ok (.error "Timeout", m))) := rfl

def nestedFailed : MM Mem (Except ErrName Nat) := pure (.error "Timeout")

/-- Triple postconditions see the state runner's pair, while source outcomes describe its value. -/
def stateFailed : MM Nat (Except ErrName Nat) := pure (.error "Timeout")

theorem stateErrorOnly (s : Nat) :
    FTotalTriple emp (stateFailed.run s) (fun r => ⟪r.1 = .error "Timeout"⟫ ⋆ emp) := by
  unfold stateFailed
  fsym

nonvacuity_witness stateErrorOnly := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem stateErased (s : Nat) : FTotalTriple emp (stateFailed.run s) (fun _ => emp) := by
  unfold stateFailed
  fsym

nonvacuity_witness stateErased := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

/-- A genuine tuple-valued source return retains its ordinary-value classification. -/
def statePair : MM Nat (Except ErrName Nat × Nat) := pure (.error "Timeout", 7)

theorem statePairOnly (s : Nat) :
    FTotalTriple emp (statePair.run s) (fun r => ⟪r.1 = (.error "Timeout", 7)⟫ ⋆ emp) := by
  unfold statePair
  fsym

nonvacuity_witness statePairOnly := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

/-- CM's scheduler computation is a terminal effect, not an unknown plain function. -/
def concurrentFailed : CM Unit Nat (Except ErrName Nat) := pure (.error "Timeout")

theorem concurrentErrorOnly (s : Nat) :
    CTriple emp (concurrentFailed.run s) (fun r => ⟪r.1 = .error "Timeout"⟫ ⋆ emp) := by
  unfold concurrentFailed
  fsym

nonvacuity_witness concurrentErrorOnly :=
  ⟨0, CAdmit.of (FTTAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl)⟩
liveness_witness concurrentErrorOnly :=
  ⟨0, CLive.of_run 1 (FTTLive.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl ⟨_, rfl⟩)⟩

theorem concurrentErased (s : Nat) : CTriple emp (concurrentFailed.run s) (fun _ => emp) := by
  unfold concurrentFailed
  fsym

nonvacuity_witness concurrentErased :=
  ⟨0, CAdmit.of (FTTAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl)⟩
liveness_witness concurrentErased :=
  ⟨0, CLive.of_run 1 (FTTLive.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl ⟨_, rfl⟩)⟩

theorem concurrentProjected (s : Nat) :
    CTriple emp (concurrentFailed.run' s) (fun r => ⟪r = .error "Timeout"⟫ ⋆ emp) := by
  unfold concurrentFailed
  fsym

nonvacuity_witness concurrentProjected :=
  ⟨0, CAdmit.of (FTTAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl)⟩
liveness_witness concurrentProjected :=
  ⟨0, CLive.of_run 1 (FTTLive.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl ⟨_, rfl⟩)⟩

/-- Explicit type arguments must not reinterpret a remaining inner state layer as ReaderT. -/
theorem nestedViaReader (s t : Mem) :
    ReaderT.run (@StateT.run Mem (ReaderT Mem Result) (Except ErrName Nat × Mem) nestedFailed s) t =
      some (.ok ((.error "Timeout", s), t)) := rfl
theorem nestedPrime (s t : Mem) : ((nestedFailed.run' s).run t).run =
    some (.ok (.error "Timeout", t)) := rfl

def readerNestedFailed : StateT Mem (ReaderT Mem Result) (Except ErrName Nat) := pure (.error "Timeout")
theorem readerNestedPrime (s t : Mem) : ReaderT.run (readerNestedFailed.run' s) t =
    some (.ok (.error "Timeout")) := rfl

/-- A runner's explicit dictionary can fabricate a successful result; it is not a source proof. -/
@[instance_reducible] def fabricatedFunctor : Functor (fun _ : Type => Result (Except ErrName Nat × Mem)) where
  map _ _ := some (.ok (.ok 0, {}))

theorem fabricatedProjection (m : Mem) :
    @StateT.run' Mem (fun _ : Type => Result (Except ErrName Nat × Mem)) fabricatedFunctor Nat failed m =
      some (.ok (.ok 0, {})) := rfl

/-- A `pure` spelling with a custom dictionary need not return at all. -/
@[instance_reducible] def divergingPure : Pure Result where
  pure _ := none

def disguisedStop : Result Nat := none
theorem fabricatedPureSuccess : disguisedStop = @Pure.pure Result divergingPure Nat 0 := rfl

/-- A plain function does not declare which part, if any, is a final state. -/
def plainPair : Nat → Result (Except ErrName Nat × Nat) := readerPair
theorem plainFunction : plainPair = readerPair := rfl
theorem plainRun (n : Nat) : ReaderT.run plainPair n = some (.ok (.error "Timeout", n)) := rfl

/-- Opaque function spelling cannot turn an unknown family into an ordinary-value equation. -/
@[irreducible] def HiddenFunction : Type := Nat → Result (Nat × Nat)
def hiddenFunction : HiddenFunction := by unfold HiddenFunction; exact (pure 0 : M Nat Nat)
theorem hiddenFunctionEquation :
    hiddenFunction = (by unfold HiddenFunction; exact (pure 0 : M Nat Nat)) := rfl

/-- A data constructor that resembles a successful Result is not a declared execution family. -/
def ordinaryOption : Option (Except String Nat) := some (.ok 0)
theorem ordinaryOptionEquation : ordinaryOption = some (.ok 0) := rfl
def partialOption : Option (Nat → Except String Nat) := some (@Except.ok String Nat)
theorem partialOptionEquation : partialOption = some (@Except.ok String Nat) := rfl

/-- Exact failed runs retain the taxonomy's distinct model constructors. -/
def failure (e : Error) : MemM Nat := throw e
theorem panic (m : Mem) : ((failure .panic).run m).run = some (.error .panic) := rfl
theorem illegal (m : Mem) : ((failure .illegal).run m).run = some (.error .illegal) := rfl
theorem unspecified (m : Mem) : ((failure .unspecified).run m).run = some (.error .unspecified) := rfl
theorem timer (m : Mem) : ((failure .unsupportedTimer).run m).run = some (.error .unsupportedTimer) := rfl
theorem deadlock (m : Mem) : ((failure .deadlock).run m).run = some (.error .deadlock) := rfl
theorem trap (m : Mem) : ((failure .trap).run m).run = some (.error .trap) := rfl
theorem stack (m : Mem) : ((failure .stackOverflow).run m).run = some (.error .stackOverflow) := rfl

/-- Direct application consumes the same declared effects as an explicit preserving runner. -/
theorem probeDirectErrorOnly (s : Nat) :
    FTotalTriple emp (stateFailed s) (fun r => ⟪r.1 = .error "Timeout"⟫ ⋆ emp) :=
  stateErrorOnly s

nonvacuity_witness probeDirectErrorOnly := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem probeConcDirect (s : Nat) :
    CTriple emp (concurrentFailed s) (fun r => ⟪r.1 = .error "Timeout"⟫ ⋆ emp) :=
  concurrentErrorOnly s

nonvacuity_witness probeConcDirect :=
  ⟨0, CAdmit.of (FTTAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl)⟩
liveness_witness probeConcDirect :=
  ⟨0, CLive.of_run 1 (FTTLive.of_mem ⟨rfl, rfl, rfl⟩ fseq_default rfl ⟨_, rfl⟩)⟩

theorem probeExactDirect (m : Mem) : failed m = some (.ok (.error "Timeout", m)) := rfl
theorem probeExactNested (s : Nat) (m : Mem) :
    (stateFailed s).run m = some (.ok ((.error "Timeout", s), m)) := rfl

theorem overappliedRun (s : Nat) (m : Mem) :
    StateT.run stateFailed s m = some (.ok ((.error "Timeout", s), m)) := rfl
theorem overappliedProjection (s : Nat) (m : Mem) :
    StateT.run' stateFailed s m = some (.ok (.error "Timeout", m)) := rfl

@[instance_reducible] def stoppingFunctor : Functor MemM where
  map _ _ := fun _ => none

theorem noncanonicalOverappliedProjection (s : Nat) (m : Mem) :
    @StateT.run' Nat MemM stoppingFunctor (Except ErrName Nat) stateFailed s m = none := rfl

theorem directTuple (s : Nat) :
    FTotalTriple emp (statePair s) (fun r => ⟪r.1 = (.error "Timeout", 7)⟫ ⋆ emp) :=
  statePairOnly s

nonvacuity_witness directTuple := ⟨0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

theorem directReader (n : Nat) : readerPair n = some (.ok (.error "Timeout", n)) := rfl

def parameterizedState (f : Nat → Nat) (n : Nat) : MM Nat (Except ErrName Nat) := pure (.ok (f n))

theorem explicitParameters (f : Nat → Nat) (n s : Nat) :
    FTotalTriple emp ((parameterizedState f n).run s) (fun r => ⟪r.1 = .ok (f n)⟫ ⋆ emp) := by
  unfold parameterizedState
  fsym

theorem directParameters (f : Nat → Nat) (n s : Nat) :
    FTotalTriple emp (parameterizedState f n s) (fun r => ⟪r.1 = .ok (f n)⟫ ⋆ emp) :=
  explicitParameters f n s

nonvacuity_witness directParameters :=
  ⟨id, 0, 0, FAdmit.of_mem ⟨rfl, rfl, rfl⟩ fseq_default⟩

def identityAt (α : Type) (value : α) : α := value

/-- Instantiating a head parameter by a function type does not add head parameters. -/
theorem dependentHead (s : Nat) :
    FTotalTriple emp (identityAt (MM Nat (Except ErrName Nat)) stateFailed s)
      (fun r => ⟪r.1 = .error "Timeout"⟫ ⋆ emp) :=
  stateErrorOnly s

end OutcomeContracts
