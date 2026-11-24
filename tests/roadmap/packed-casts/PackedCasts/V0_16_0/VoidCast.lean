-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace PackedCasts.V0_16_0.VoidCast

structure intToVoidsLocals where
  deriving Inhabited

inductive intToVoidsExit where
  | ret (v : Vector (Unit) 4)

def intToVoids  : Zig.Result (Vector (Unit) 4) := do
  let e ← ((do
    let i0 ← Zig.reprCast (Vector (Unit) 4) ((0 : BitVec 0) : BitVec 0)
    pure (.ret i0)) : Zig.M intToVoidsLocals intToVoidsExit).run' (default : intToVoidsLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] intToVoids

structure voidsToIntLocals where
  deriving Inhabited

inductive voidsToIntExit where
  | ret (v : BitVec 0)

def voidsToInt  : Zig.Result (BitVec 0) := do
  let e ← ((do
    let i0 ← Zig.reprCast (BitVec 0) ((#v[(), (), (), ()] : Vector (Unit) 4) : Vector (Unit) 4)
    pure (.ret i0)) : Zig.M voidsToIntLocals voidsToIntExit).run' (default : voidsToIntLocals)
  match e with
  | .ret v => pure v

attribute [zig_run] voidsToInt

end PackedCasts.V0_16_0.VoidCast