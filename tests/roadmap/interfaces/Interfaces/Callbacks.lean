-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
-- air2lean-models: {"assumptions":["extern:ext_visit"],"bindings":[{"contract":"CallbackModel.contract","dependencies":[],"effects":"tracked","errors":["illegal","stackOverflow"],"extern":{"library":null,"premise":"EXT-03"},"footprint":{"reads":[],"writes":[0]},"implementation":"CallbackModel.visit","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"},"proof":null,"signature":{"params":[{"children":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int false 32"}],"layout":{"align":8,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":4,"sentinel":false,"size":8,"volatile":false},"type":"Air2Lean.Ty.ptr \"one\" false 0"},{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int false 32"}],"return":{"children":[],"layout":{"align":1,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":1,"volatile":false},"type":"Air2Lean.Ty.bool"}},"symbol":"extern:ext_visit","termination":"partial","trust":"assumed"}],"qualification":"selected-sequential-direct-MemM-models","schema":1}
-- air2lean-interfaces: {"ext":[{"field":"call0","type":"fn (*u32, u32) callconv(.c) bool"}],"interfaces":[{"contract":"Interfaces.CallbacksSpec.visitPre","function":"fn (*u32, u32) callconv(.c) bool","interface":"Visitor","premise":"EXT-05"}]}
import ZigLean

import CallbackModel


namespace Interfaces.Callbacks

structure Ops where
  visit : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Ops where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.visit)]
  decode bs := do pure { visit := ← Zig.Enc.decodeAt bs 0 }

def air2lean_model_0_contract : Zig.External.Contract ((Zig.Ptr) × (BitVec 32)) (Bool) := _root_.CallbackModel.contract

def air2lean_model_0 (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Bool) := Zig.External.claim p0 .write *> _root_.CallbackModel.visit (p0, p1)

def air2lean_model_0_footprint : Zig.External.Footprint ((Zig.Ptr) × (BitVec 32)) where
  reads := fun _ => []
  writes := fun args => [Zig.External.Region.block args.1]

-- Explicit imported-model assumption; reported in air2lean-models.
axiom air2lean_model_0_evidence : air2lean_model_0_contract.Holds .«partial» [Zig.Error.illegal, Zig.Error.stackOverflow] .tracked _root_.CallbackModel.visit ∧ air2lean_model_0_contract.Respects air2lean_model_0_footprint

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ [
  -- 0: callbacks.ext_ops
  (Zig.Enc.encode (({ visit := (⟨some 1, 0⟩ : Zig.Ptr) } : Ops) : Ops), 8, .constGlobal),
  -- 1: extern:ext_visit
  (#[.undef], 1, .constGlobal),
  -- 2: callbacks.sum_ops
  (Zig.Enc.encode (({ visit := (⟨some 3, 0⟩ : Zig.Ptr) } : Ops) : Ops), 8, .constGlobal),
  -- 3: callbacks.sumVisit
  (#[.undef], 1, .constGlobal)]

/-- The spawn targets of the program. -/
inductive Tgt where

/-- The environment's implementations of the open interfaces (`docs/interfaces.md`,
premise EXT-05): `call<i> f args` runs the environment's function at `f`, a pointer that is no
function of the program. -/
class Ext where
  /-- `fn (*u32, u32) callconv(.c) bool` -/
  call0 : Zig.Ptr → (Zig.Ptr) → (BitVec 32) → Zig.ConcM Tgt (Bool)

/-- The closed program's environment: no function besides the program's. -/
@[reducible] def Ext.closed : Ext where
  call0 _ _ _ := throw .illegal

structure sumVisitLocals where
  deriving Inhabited

inductive sumVisitExit where
  | ret (v : Bool)

def sumVisit (p0 : Zig.Ptr) (p1 : BitVec 32) : Zig.MemM (Bool) := do
  let e ← ((do
    let i2 ← Zig.load (BitVec 32) 4 p0
    let i3 ← pure (Zig.addWrap i2 p1)
    Zig.store (α := BitVec 32) 4 p0 i3
    pure (.ret true)) : Zig.MM sumVisitLocals sumVisitExit).run' (default : sumVisitLocals)
  match e with
  | .ret v => pure v

structure callOpsLocals where
  deriving Inhabited

inductive callOpsExit where
  | ret (v : Bool)

def callOps [Ext] (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i3 ← pure p0
    let i4 ← Zig.load (Zig.Ptr) 8 i3
    let i5 ← (if i4 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callMC (air2lean_model_0 p1 p2) else if i4 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (sumVisit p1 p2) else Zig.callC (Zig.extCall (Ext.call0 i4 p1 p2)))
    pure (.ret i5)) : Zig.CM Tgt callOpsLocals callOpsExit).run' (default : callOpsLocals)
  match e with
  | .ret v => pure v

structure evaluateLocals where
  deriving Inhabited

inductive evaluateExit where
  | ret (v : Bool)

def evaluate [Ext] (p0 : Zig.Ptr) (p1 : Zig.Ptr) (p2 : BitVec 32) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i3 ← (if p0 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callMC (air2lean_model_0 p1 p2) else if p0 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (sumVisit p1 p2) else Zig.callC (Zig.extCall (Ext.call0 p0 p1 p2)))
    pure (.ret i3)) : Zig.CM Tgt evaluateLocals evaluateExit).run' (default : evaluateLocals)
  match e with
  | .ret v => pure v

structure forEachLocals where
  local3 : BitVec 64
  deriving Inhabited

inductive forEachExit where
  | ret (v : Bool)
  | br15
  | br9
  | br6
  | rep7

def forEach.again7 : forEachExit → Bool
  | .rep7 => true
  | _ => false

def forEach.loop7 [Ext] (p0 : Zig.Slice) (p1 : Zig.Ptr) (p2 : Zig.Ptr) (i5 : BitVec 64) : Zig.CM Tgt forEachLocals forEachExit := do
  let i8 ← pure ((← get).local3)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (i5)
    let i12 ← pure (Zig.lt false i10 i11)
    if i12 then (do
      let i14 ← Zig.callMC (Zig.checkIndex p0.len i8 >>= fun _ => Zig.load (BitVec 32) 4 (p0.ptr.elem 4 i8))
      match ← ((do
        let i16 ← (if p2 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callMC (air2lean_model_0 p1 i14) else if p2 == (⟨some 3, 0⟩ : Zig.Ptr) then Zig.callMC (sumVisit p1 i14) else Zig.callC (Zig.extCall (Ext.call0 p2 p1 i14)))
        let i17 ← pure (!i16)
        if i17 then (do
          pure (.ret false))
        else (do
          pure .br15)) : Zig.CM Tgt forEachLocals forEachExit) with
      | .br15 => (do
        pure .br9)
      | e => pure e)
    else (do
      pure .br6)) : Zig.CM Tgt forEachLocals forEachExit) with
  | .br9 => (do
    let i23 ← Zig.add false i8 (1 : BitVec 64) (safe := false)
    modify (fun s => { s with local3 := i23 })
    pure .rep7)
  | e => pure e

def forEach [Ext] (p0 : Zig.Slice) (p1 : Zig.Ptr) (p2 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    let i5 ← pure p0.len
    match ← ((do
      Zig.loop (forEach.loop7 p0 p1 p2 i5) forEach.again7) : Zig.CM Tgt forEachLocals forEachExit) with
    | .br6 => (do
      pure (.ret true))
    | e => pure e) : Zig.CM Tgt forEachLocals forEachExit).run' (default : forEachLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure viaOpsLocals where
  deriving Inhabited

inductive viaOpsExit where
  | ret (v : Bool)

def viaOps [Ext] (p0 : Zig.Ptr) (p1 : Zig.Slice) (p2 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i3 ← pure p0
    let i4 ← Zig.load (Zig.Ptr) 8 i3
    let i5 ← Zig.callC (forEach p1 p2 i4)
    pure (.ret i5)) : Zig.CM Tgt viaOpsLocals viaOpsExit).run' (default : viaOpsLocals)
  match e with
  | .ret v => pure v

structure runExternalLocals where
  deriving Inhabited

inductive runExternalExit where
  | ret (v : Bool)

def runExternal [Ext] (p0 : Zig.Slice) (p1 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i2 ← Zig.callC (viaOps (⟨some 0, 0⟩ : Zig.Ptr) p0 p1)
    pure (.ret i2)) : Zig.CM Tgt runExternalLocals runExternalExit).run' (default : runExternalLocals)
  match e with
  | .ret v => pure v

structure runLocalLocals where
  deriving Inhabited

inductive runLocalExit where
  | ret (v : Bool)

def runLocal [Ext] (p0 : Zig.Slice) (p1 : Zig.Ptr) : Zig.ConcM Tgt (Bool) := do
  let e ← ((do
    let i2 ← Zig.callC (viaOps (⟨some 2, 0⟩ : Zig.Ptr) p0 p1)
    pure (.ret i2)) : Zig.CM Tgt runLocalLocals runLocalExit).run' (default : runLocalLocals)
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch [Ext] : Tgt → Zig.ConcM Tgt Unit :=
  fun t => nomatch t

end Interfaces.Callbacks