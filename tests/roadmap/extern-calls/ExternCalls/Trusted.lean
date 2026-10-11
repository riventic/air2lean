-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
-- air2lean-models: {"assumptions":["extern:abs"],"bindings":[{"contract":"ExternModel.absContract","dependencies":[],"effects":"preserves","errors":["illegal"],"extern":{"library":"c","premise":"EXT-03"},"footprint":null,"implementation":"ExternModel.abs","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"},"proof":null,"signature":{"params":[{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"}],"return":{"children":[],"layout":{"align":4,"allowzero":false,"bit_offset":0,"host_size":0,"offsets":[],"pointer_align":null,"sentinel":false,"size":4,"volatile":false},"type":"Air2Lean.Ty.int true 32"}},"symbol":"extern:abs","termination":"total","trust":"assumed"}],"qualification":"selected-sequential-direct-MemM-models","schema":1}
import ZigLean

import ExternModel


namespace ExternCalls.Trusted

def air2lean_model_0_contract : Zig.External.Contract ((BitVec 32)) (BitVec 32) := _root_.ExternModel.absContract

def air2lean_model_0 (p0 : BitVec 32) : Zig.MemM (BitVec 32) := _root_.ExternModel.abs p0

-- Explicit imported-model assumption; reported in air2lean-models.
axiom air2lean_model_0_evidence : air2lean_model_0_contract.Holds .total [Zig.Error.illegal] .preserves _root_.ExternModel.abs

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure absSumLocals where
  deriving Inhabited

inductive absSumExit where
  | ret (v : BitVec 32)

def absSum (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.callM (air2lean_model_0 p0)
    let i3 ← Zig.callM (air2lean_model_0 p1)
    let i4 ← pure (Zig.addWrap i2 i3)
    pure (.ret i4)) : Zig.MM absSumLocals absSumExit).run' (default : absSumLocals)
  match e with
  | .ret v => pure v

end ExternCalls.Trusted