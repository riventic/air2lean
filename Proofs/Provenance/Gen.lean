-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace Provenance

structure addLocals where
  deriving Inhabited

inductive addExit where
  | ret (v : BitVec 32)

def add (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.addWrap p0 p1)
    pure (.ret i2)) : Zig.M addLocals addExit).run' (default : addLocals)
  match e with
  | .ret v => pure v

structure doubleLocals where
  deriving Inhabited

inductive doubleExit where
  | ret (v : BitVec 32)

def double (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.call (add p0 p0)
    pure (.ret i1)) : Zig.M doubleLocals doubleExit).run' (default : doubleLocals)
  match e with
  | .ret v => pure v

end Provenance