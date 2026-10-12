-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
-- air2lean-models: {"assumptions":["extern:ext_visit"],"bindings":[{"contract":"CallbackModel.contract","dependencies":[],"effects":"tracked","errors":["overflow","outOfBounds","divByZero","unreachable","panic","unspecified","illegal","deadlock","unsupportedTimer","trap","stackOverflow"],"extern":{"library":null,"premise":"EXT-03"},"footprint":{"reads":[],"writes":[0]},"implementation":"CallbackModel.visit","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"},"proof":null,"signature":{"params":[{"children":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int false 32"}],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":4,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.ptr \"one\" false 0"},{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int false 32"}],"return":{"children":[],"layout":{"align":1,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":1,"volatile":false},"type":"Air2Lean.Ty.bool"}},"symbol":"extern:ext_visit","termination":"partial","trust":"assumed"}],"qualification":"selected-sequential-direct-MemM-models","schema":1}
import ZigLean

import CallbackModel


namespace Callbacks.Async

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

def air2lean_model_0_contract : Zig.External.Contract ((Zig.Ptr) × (BitVec 32)) (Bool) := _root_.CallbackModel.contract

def air2lean_model_0 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Bool) := Zig.External.claim p0 .write *> _root_.CallbackModel.visit (p0, p1)

def air2lean_model_0_footprint : Zig.External.Footprint ((Zig.Ptr) × (BitVec 32)) where
  reads := fun _ => []
  writes := fun args => [Zig.External.Region.block args.1]

-- Explicit imported-model assumption; reported in air2lean-models.
axiom air2lean_model_0_evidence : air2lean_model_0_contract.Holds .«partial» [Zig.Error.overflow, Zig.Error.outOfBounds, Zig.Error.divByZero, Zig.Error.unreachable, Zig.Error.panic, Zig.Error.unspecified, Zig.Error.illegal, Zig.Error.deadlock, Zig.Error.unsupportedTimer, Zig.Error.trap, Zig.Error.stackOverflow] .tracked _root_.CallbackModel.visit ∧ air2lean_model_0_contract.Respects air2lean_model_0_footprint

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: extern:ext_visit
  (#[.undef], 1, .constGlobal)]

/-- The spawn targets of the program; fields are captured by value. -/
inductive Tgt where
  | worker (a : (Zig.Ptr) × (Zig.Ptr) × (BitVec 32))

/-- The child protocol obligation for the complete captured tuple. Pointer
identities are copied; a proof must explicitly justify ownership transfer or sharing. -/
abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=
  P.init target ghost

/-- Each captured field in source order. A value is copied and carries no ownership;
a pointer or slice copies only its identity, so a spawn proof must hand over or share its
region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/
def Tgt.captures : Tgt → List Zig.Conc.Capture
  | .worker (capture0, capture1, _) => [.ptr capture0, .ptr capture1, .value]

structure workerLocals where
  deriving Inhabited

inductive workerExit where
  | ret

def worker (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) : Zig.MemM (Unit) := do
  let e ← ((do
    let _i3 ← (if p0 == (⟨some 0, 0⟩ : Zig.Ptr) then Zig.callM (air2lean_model_0 p1 p2) else throw .illegal)
    pure .ret) : Zig.MM workerLocals workerExit).run' (default : workerLocals)
  match e with
  | .ret => pure ()

structure runBothLocals where
  deriving Inhabited

inductive runBothExit where
  | ret (v : Except Zig.ErrName (Unit))

def runBoth (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : Zig.Ptr) (p3 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i4 ← pure (p0, p1, p3)
    let i5 ← Zig.spawnC (Tgt.worker i4)
    match i5 with
    | .error _ => (do
      let i7 ← Zig.callRC (Zig.unwrapErr i5)
      let i8 ← pure (i7)
      let i9 ← pure ((.error i8) : Except Zig.ErrName (Unit))
      pure (.ret i9))
    | .ok v6 => (do
      let _i11 ← Zig.callMC (worker p0 p2 p3)
      let _i12 ← Zig.joinC v6
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt runBothLocals runBothExit).run' (default : runBothLocals)
  match e with
  | .ret v => pure v

structure runExternalLocals where
  deriving Inhabited

inductive runExternalExit where
  | ret (v : Except Zig.ErrName (Unit))

def runExternal (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) : Zig.ConcM Tgt (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    let i3 ← Zig.callC (runBoth (⟨some 0, 0⟩ : Zig.Ptr) p0 p1 p2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callRC (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (Unit))
      pure (.ret i7))
    | .ok _v4 => (do
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.CM Tgt runExternalLocals runExternalExit).run' (default : runExternalLocals)
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .worker a =>
    let (capture0, capture1, capture2) := a
    discard (Zig.ConcM.liftMem (worker capture0 capture1 capture2))

end Callbacks.Async