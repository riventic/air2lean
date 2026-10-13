-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace EncExactness.Opaque

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

structure allocatorWordLocals where
  c : Zig.Ptr
  deriving Inhabited

inductive allocatorWordExit where
  | ret (v : BitVec 64)

-- air2lean-premises: {"ALC-09":[0]}
def allocatorWord (p0 : Zig.Allocator) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 16 8
  let e ← ((do
    let i1 ← pure (← get).c
    Zig.store (α := Zig.Allocator) 8 i1 p0
    let i3 ← pure (i1)
    let i4 ← Zig.callM (Zig.load (BitVec 64) 8 (i3.elem 8 (1 : BitVec 64)))
    pure (.ret i4)) : Zig.MM allocatorWordLocals allocatorWordExit).run' { (default : allocatorWordLocals) with c := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v

end EncExactness.Opaque